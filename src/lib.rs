#![no_std]

use cortex_m::{asm, peripheral::MPU};

pub use arrayvec::ArrayVec;
/// Enable bit in MPU_CTRL
const CTRL_ENABLE: u32 = 1 << 0;
/// Enable for hard fault and non-maskable interrupt bit in MPU_CTRL
const _CTRL_HFNMIENA: u32 = 1 << 1;
/// Default memory map for privileged mode bit in MPU_CTRL
const CTRL_PRIVDEFENA: u32 = 1 << 2;

fn update_mpu_unprivileged(mpu: &mut MPU, f: impl FnOnce(&mut MPU)) {
    // Atomic MPU updates:
    // Turn off interrupts, turn off MPU, reconfigure, turn it back on, reenable interrupts.
    // Turning off interrupts is not needed when the old configuration only applied to
    // unprivileged thread code: The entire operation is interruptible, as long as the
    // processor is never made to run any other thread-mode code.

    // https://developer.arm.com/docs/dui0553/latest/cortex-m4-peripherals/optional-memory-protection-unit/updating-an-mpu-region
    asm::dsb();

    // Disable MPU while we update the regions
    unsafe {
        mpu.ctrl.write(0);
    }

    f(mpu);

    unsafe {
        // Enable MPU, but not for privileged code
        mpu.ctrl.write(CTRL_ENABLE | CTRL_PRIVDEFENA);
    }

    asm::dsb();
    asm::isb();
}

unsafe fn update_mpu_privileged(mpu: &mut MPU, f: impl FnOnce(&mut MPU)) {
    // Atomic MPU updates:
    // Turn off interrupts, turn off MPU, reconfigure, turn it back on, reenable interrupts.
    // https://developer.arm.com/docs/dui0553/latest/cortex-m4-peripherals/optional-memory-protection-unit/updating-an-mpu-region
    asm::dsb();
    cortex_m::interrupt::free(|_| {
        // Disable MPU while we update the regions
        unsafe {
            mpu.ctrl.write(0);
        }

        f(mpu);

        unsafe {
            // Enable MPU for privileged and unprivileged code
            mpu.ctrl.write(CTRL_ENABLE);
        }
    });

    asm::dsb();
    asm::isb();
}

/// The Cortex-M0+ MPU.
pub mod cortex_m0p {
    use super::*;

    /// Wrapper around the Cortex-M0+ Memory Protection Unit (MPU).
    pub struct Mpu(MPU);

    impl Mpu {
        /// The smallest supported region size.
        pub const MIN_REGION_SIZE: Size = Size::S256B;

        /// Number of supported memory regions.
        pub const REGION_COUNT: u8 = 8;

        const REGION_COUNT_USIZE: usize = Self::REGION_COUNT as usize;

        /// Creates a new MPU wrapper, taking ownership of the `MPU` peripheral.
        ///
        /// # Safety
        ///
        /// This function is safe to call if the processor is a Cortex-M0+ and has an MPU.
        pub unsafe fn new(raw: MPU) -> Self {
            Mpu(raw)
        }

        /// Consumes `self` and returns the raw MPU peripheral.
        pub fn into_inner(self) -> MPU {
            self.0
        }

        /// Configures the MPU to restrict access to software running in unprivileged mode.
        ///
        /// Any violation of the MPU settings will cause a *HardFault* exception. The Cortex-M0+
        /// does not have a dedicated memory management exception.
        ///
        /// Unprivileged code will only be allowed to access memory inside one of the given
        /// `regions`.
        ///
        /// Code running in privileged mode will not be restricted by the MPU, except that regions
        /// that have `executable` set to `false` will be marked as ***N**ever e**X**excute* (`NX`),
        /// which is enforced even for privileged code.
        pub fn configure_unprivileged(
            &mut self,
            regions: &ArrayVec<[Region; Self::REGION_COUNT_USIZE]>,
        ) {
            // Safety: This is safe because it does not affect the privileged code calling it.
            // Unprivileged, untrusted (non-Rust) code is always unsafe to call, so this doesn't
            // have to be unsafe as well. If called by unprivileged code, the register writes will
            // fault, which is also safe.

            update_mpu_unprivileged(&mut self.0, |mpu| {
                for (i, region) in regions.iter().enumerate() {
                    unsafe {
                        {
                            let addr = (region.base_addr as u32) & !0b11111;
                            let valid = 1 << 4;
                            let region = i as u32;
                            mpu.rbar.write(addr | valid | region);
                        }

                        {
                            let xn = if region.executable { 0 } else { 1 << 28 };
                            let ap = (region.permissions as u32) << 24;
                            let scb = region.attributes.to_bits() << 16;
                            let srd = u32::from(region.subregions.bits()) << 8;
                            let size = u32::from(region.size.bits()) << 1;
                            let enable = 1;

                            mpu.rasr.write(xn | ap | scb | srd | size | enable);
                        }
                    }
                }

                // Disable the remaining regions
                for i in regions.len()..usize::from(Self::REGION_COUNT) {
                    unsafe {
                        let addr = 0;
                        let valid = 1 << 4;
                        let region = i as u32;
                        mpu.rbar.write(addr | valid | region);

                        mpu.rasr.write(0); // disable region
                    }
                }
            });
        }
    }

    /// Memory region properties.
    #[derive(Debug, Copy, Clone)]
    pub struct Region {
        /// Starting address of the region (lowest address).
        ///
        /// This must be aligned to the region's `size`.
        pub base_addr: usize,
        /// Size of the region.
        pub size: Size,
        /// The subregions to enable or disable.
        pub subregions: Subregions,
        /// Whether to allow instruction fetches from this region.
        ///
        /// If this is `false`, the region will be marked as NX (Never eXecute).
        /// This affects both privileged and unprivileged code, regardless of
        /// other MPU settings.
        pub executable: bool,
        /// Data access permissions for the region.
        pub permissions: AccessPermission,
        /// Memory type and cache policy attributes.
        pub attributes: MemoryAttributes,
    }

    /// Describes memory type, cache policy, and shareability.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum MemoryAttributes {
        /// Shareable, non-cached, strongly-ordered memory region.
        StronglyOrdered,

        /// Non-cached device peripheral region. Always considered shareable.
        Device,

        /// Normal memory region (ie. "actual" memory, such as Flash or SRAM).
        Normal {
            /// Whether the region is accessible by more than one bus master
            /// (eg. a DMA engine or a second MCU core).
            shareable: bool,

            /// Cache policy of the region.
            cache_policy: CachePolicy,
        },
    }

    impl MemoryAttributes {
        /// Turns `self` into its bit-level representation, in order `0bSCB`.
        fn to_bits(self) -> u32 {
            macro_rules! bits {
                ( C=$c:literal, B=$b:literal, S=$s:ident ) => {
                    (if $s { 1 } else { 0 } << 2) | ($c << 1) | $b
                };
                ( C=$c:literal, B=$b:literal, S=$s:literal ) => {
                    ($s << 2) | ($c << 1) | $b
                };
            }

            match self {
                Self::StronglyOrdered => bits!(C = 0, B = 0, S = 0),
                Self::Device => bits!(C = 0, B = 1, S = 0),
                Self::Normal {
                    shareable,
                    cache_policy,
                } => match cache_policy {
                    CachePolicy::WriteThrough => bits!(C = 1, B = 0, S = shareable),
                    CachePolicy::WriteBack => bits!(C = 1, B = 1, S = shareable),
                },
            }
        }
    }

    /// The caching policy for a "normal" memory region.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum CachePolicy {
        /// Write-through, no write allocate.
        WriteThrough,

        /// Write-back cacheable region, no write-allocate.
        WriteBack,
    }
}

/// The Cortex-M4 MPU.
pub mod cortex_m4 {
    use super::*;

    /// Wrapper around the Cortex-M4 Memory Protection Unit (MPU).
    pub struct Mpu(MPU);

    impl Mpu {
        /// The smallest supported region size.
        pub const MIN_REGION_SIZE: Size = Size::S32B;

        /// Number of supported memory regions.
        pub const REGION_COUNT: u8 = 8;

        const REGION_COUNT_USIZE: usize = Self::REGION_COUNT as usize;

        /// Creates a new MPU wrapper, taking ownership of the `MPU` peripheral.
        ///
        /// # Safety
        ///
        /// This is safe to call if the processor is a Cortex-M4 or M4F and has an MPU.
        pub unsafe fn new(raw: MPU) -> Self {
            Mpu(raw)
        }

        /// Consumes `self` and returns the raw MPU peripheral.
        pub fn into_inner(self) -> MPU {
            self.0
        }

        /// Configures the MPU to restrict access to software running in unprivileged mode.
        ///
        /// Code running in privileged mode will not be restricted by the MPU.
        pub fn configure_unprivileged(
            &mut self,
            regions: &ArrayVec<[Region; Self::REGION_COUNT_USIZE]>,
        ) {
            // Safety: This is safe because it does not affect the privileged code calling it.
            // Unprivileged, untrusted (non-Rust) code is always unsafe to call, so this doesn't
            // have to be unsafe as well. If called by unprivileged code, the register writes will
            // fault, which is also safe.

            update_mpu_unprivileged(&mut self.0, |mpu| {
                for (i, region) in regions.iter().enumerate() {
                    unsafe {
                        {
                            let addr = (region.base_addr as u32) & !0b11111;
                            let valid = 1 << 4;
                            let region = i as u32;
                            mpu.rbar.write(addr | valid | region);
                        }

                        {
                            let xn = if region.executable { 0 } else { 1 << 28 };
                            let ap = (region.permissions as u32) << 24;
                            let texscb = region.attributes.to_bits() << 16;
                            let srd = u32::from(region.subregions.bits()) << 8;
                            let size = u32::from(region.size.bits()) << 1;
                            let enable = 1;

                            mpu.rasr.write(xn | ap | texscb | srd | size | enable);
                        }
                    }
                }

                // Disable the remaining regions
                for i in regions.len()..usize::from(Self::REGION_COUNT) {
                    unsafe {
                        let addr = 0;
                        let valid = 1 << 4;
                        let region = i as u32;
                        mpu.rbar.write(addr | valid | region);

                        mpu.rasr.write(0); // disable region
                    }
                }
            });
        }

        /// Configures the MPU to restrict access to software running in both privileged and
        /// unprivileged modes
        pub unsafe fn configure_privileged(
            &mut self,
            regions: &ArrayVec<[Region<FullAccessPermissions>; Self::REGION_COUNT_USIZE]>,
        ) {
            update_mpu_privileged(&mut self.0, |mpu| {
                for (i, region) in regions.iter().enumerate() {
                    unsafe {
                        {
                            let addr = (region.base_addr as u32) & !0b11111;
                            let valid = 1 << 4;
                            let region = i as u32;
                            mpu.rbar.write(addr | valid | region);
                        }

                        {
                            let xn = if region.executable { 0 } else { 1 << 28 };
                            let ap = (region.permissions as u32) << 24;
                            let texscb = region.attributes.to_bits() << 16;
                            let srd = u32::from(region.subregions.bits()) << 8;
                            let size = u32::from(region.size.bits()) << 1;
                            let enable = 1;

                            mpu.rasr.write(xn | ap | texscb | srd | size | enable);
                        }
                    }
                }

                // Disable the remaining regions
                for i in regions.len()..usize::from(Self::REGION_COUNT) {
                    unsafe {
                        let addr = 0;
                        let valid = 1 << 4;
                        let region = i as u32;
                        mpu.rbar.write(addr | valid | region);

                        mpu.rasr.write(0); // disable region
                    }
                }
            });
        }
    }

    /// Memory region properties.
    #[derive(Debug, Copy, Clone)]
    pub struct Region<P = AccessPermission> {
        /// Starting address of the region (lowest address).
        ///
        /// This must be aligned to the region's `size`.
        pub base_addr: usize,
        /// Size of the region.
        pub size: Size,
        /// The subregions to enable or disable.
        pub subregions: Subregions,
        /// Whether to allow instruction fetches from this region.
        ///
        /// If this is `false`, the region will be marked as NX (Never eXecute).
        /// This affects both privileged and unprivileged code, regardless of
        /// other MPU settings.
        pub executable: bool,
        /// Data access permissions for the region.
        pub permissions: P,
        /// Memory type and cache policy attributes.
        pub attributes: MemoryAttributes,
    }

    /// Describes memory type, cache policy, and shareability.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum MemoryAttributes {
        /// Shareable, non-cached, strongly-ordered memory region.
        StronglyOrdered,

        /// Non-cached device peripheral region.
        Device {
            /// Whether the region is accessible by more than one bus master (eg. a
            /// DMA engine or a second MCU core).
            shareable: bool,
        },

        /// Normal memory region (ie. "actual" memory, such as Flash or SRAM).
        Normal {
            /// Whether the region is accessible by more than one bus master (eg. a
            /// DMA engine or a second MCU core).
            shareable: bool,

            /// How this region should be cached (?).
            cache_policy: CachePolicy,
        },
    }

    impl MemoryAttributes {
        /// Turns `self` into its bit-level representation, consisting of the TEX, C, B, and S bits.
        fn to_bits(self) -> u32 {
            macro_rules! bits {
                ( TEX=$tex:literal, C=$c:literal, B=$b:literal, S=$s:ident ) => {
                    ($tex << 3) | (if $s { 1 } else { 0 } << 2) | ($c << 1) | $b
                };
                ( TEX=$tex:literal, C=$c:literal, B=$b:literal, S=$s:literal ) => {
                    ($tex << 3) | ($s << 2) | ($c << 1) | $b
                };
            }

            match self {
                Self::StronglyOrdered => bits!(TEX = 0b000, C = 0, B = 0, S = 0),
                Self::Device { shareable: false } => bits!(TEX = 0b010, C = 0, B = 0, S = 0),
                Self::Device { shareable: true } => bits!(TEX = 0b000, C = 0, B = 1, S = 0),
                Self::Normal {
                    shareable,
                    cache_policy,
                } => match cache_policy {
                    CachePolicy::NonCacheable => bits!(TEX = 0b001, C = 0, B = 0, S = shareable),
                    CachePolicy::WriteThrough => bits!(TEX = 0b000, C = 1, B = 0, S = shareable),
                    CachePolicy::WriteBack {
                        write_allocate: false,
                    } => bits!(TEX = 0b000, C = 1, B = 1, S = shareable),
                    CachePolicy::WriteBack {
                        write_allocate: true,
                    } => bits!(TEX = 0b001, C = 1, B = 1, S = shareable),
                },
            }
        }
    }

    /// The caching policy for a "normal" memory region.
    #[derive(Debug, Copy, Clone, PartialEq, Eq)]
    pub enum CachePolicy {
        /// Non-cacheable memory region.
        NonCacheable,

        /// Write-through, no write allocate.
        WriteThrough,

        /// Write-back cacheable region.
        WriteBack {
            /// Whether a write miss loads the missed cache row into cache.
            write_allocate: bool,
        },
        // FIXME: There's also mixed "outer"/"inner" policies, but I don't know what that even means.
    }
}

/// Data access permissions for a memory region from unprivileged code.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum AccessPermission {
    /// Any data access (read or write) will generate a fault.
    NoAccess = 0b01,

    /// Any write access will generate a fault.
    ReadOnly = 0b10,

    /// Region unprotected, both reads and writes are allowed.
    ReadWrite = 0b11,
}

/// Data access permissions for privileged and unprivileged modes
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub enum FullAccessPermissions {
    /// Any access generates a permission fault
    PrivilegedNoAccessUnprivilegedNoAccess = 0b000,
    /// Privileged access only
    PrivilegedReadWriteUnprivilegedNoAccess = 0b001,
    /// Any unprivileged write generates a permission fault
    PrivilegedReadWriteUnprivilegedReadOnly = 0b010,
    /// Full access
    PrivilegedReadWriteUnprivilegedReadWrite = 0b011,
    /// Privileged read-only
    PrivilegedReadOnlyUnprivilegedNoAccess = 0b101,
    /// Privileged or unprivileged read-only
    PrivilegedReadOnlyUnprivilegedReadOnly = 0b110,
}

/// Subregion Disable (SRD) bits for the 8 subregions in a region.
///
/// Note that some cores do not support subregions for small region sizes. Check the core's User
/// Guide for more information.
#[derive(Debug, Copy, Clone, PartialEq, Eq)]
pub struct Subregions(u8);

impl Subregions {
    /// None of the 8 subregions are enabled. Equivalent to disabling the entire region.
    pub const NONE: Self = Subregions(0xff);

    /// All 8 subregions are enabled.
    pub const ALL: Self = Subregions(0);

    /// Creates a `Subregions` mask from raw Subregion Disable (SRD) bits.
    ///
    /// The least significant bit disables the lowest 1/8th of the region, and so on.
    pub fn from_disable_bits(bits: u8) -> Self {
        Subregions(bits)
    }

    /// Returns the raw 8-bit Subregion Disable Bits value.
    pub fn bits(self) -> u8 {
        self.0
    }
}

/// By default, all subregions are enabled.
impl Default for Subregions {
    fn default() -> Self {
        Self::ALL
    }
}

/// Memory region size value (5 bits).
///
/// Memory regions must have a size that is a power of two, and their base address must be naturally
/// aligned (ie. aligned to their size).
///
/// There is a core-specific minimum size exposed as `Mpu::MIN_REGION_SIZE`.
#[derive(Copy, Clone, Debug, PartialEq, Eq, PartialOrd, Ord)]
pub struct Size(u8);

impl Size {
    pub const S32B: Self = Size(4);

    pub const S64B: Self = Size(5);

    pub const S128B: Self = Size(6);

    pub const S256B: Self = Size(7);

    pub const S512B: Self = Size(8);

    pub const S1K: Self = Size(9);

    pub const S2K: Self = Size(10);

    pub const S4K: Self = Size(11);

    pub const S8K: Self = Size(12);

    pub const S16K: Self = Size(13);

    pub const S32K: Self = Size(14);

    pub const S64K: Self = Size(15);

    pub const S128K: Self = Size(16);

    pub const S256K: Self = Size(17);

    pub const S512K: Self = Size(18);

    pub const S1M: Self = Size(19);

    pub const S2M: Self = Size(20);

    pub const S4M: Self = Size(21);

    pub const S8M: Self = Size(22);

    pub const S16M: Self = Size(23);

    pub const S32M: Self = Size(24);

    pub const S64M: Self = Size(25);

    pub const S128M: Self = Size(26);

    pub const S256M: Self = Size(27);

    pub const S512M: Self = Size(28);

    pub const S1G: Self = Size(29);

    pub const S2G: Self = Size(30);

    /// The entire 4 GiB memory space.
    pub const S4G: Self = Size(31);

    /// Creates a `Size` from a raw 5-bit value.
    ///
    /// The `bits` encode a region size of `2^(bits + 1)`. For example, a 1 KiB region would use
    /// `0b01001` (9): `2^(9+1) = 2^10 = 1024`.
    pub const fn from_raw_bits(bits: u8) -> Self {
        Size(bits)
    }

    /// Returns the raw 5-bit value encoding the region size.
    pub const fn bits(self) -> u8 {
        self.0
    }
}
