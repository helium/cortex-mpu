#![feature(asm)]
#![no_std]
#![no_main]

use core::ptr;
use cortex_m::{
    asm,
    register::{control, lr},
};
use cortex_m_rt::{entry, exception, ExceptionFrame};
use cortex_m_semihosting::hprintln;
use cortex_mpu::{
    cortex_m0p::{CachePolicy, MemoryAttributes, Mpu, Region, Size},
    AccessPermission, ArrayVec,
};
use panic_semihosting as _;
use stm32l0xx_hal as hal;

/// Any violation of the MPU configuration results in a HardFault, since the M0(+) doesn't have
/// dedicated memory management exceptions.
#[exception]
fn HardFault(frame: &ExceptionFrame) -> ! {
    let lr = lr::read();
    hprintln!("HardFault. lr=0x{:08x} frame={:?}", lr, frame).ok();
    loop {}
}

#[exception]
fn DefaultHandler(irqn: i16) {
    hprintln!("unhandled IRQ {}", irqn).ok();
}

const MEMATTR_FLASH: MemoryAttributes = MemoryAttributes::Normal {
    shareable: true,
    cache_policy: CachePolicy::WriteThrough,
};

const MEMATTR_RAM: MemoryAttributes = MemoryAttributes::Normal {
    shareable: true,
    cache_policy: CachePolicy::WriteBack,
};

#[entry]
fn main() -> ! {
    hprintln!("\nmain()").ok();

    let core_periph = hal::pac::CorePeripherals::take().unwrap();

    // Safe: This is an STM32L072, which has a Cortex-M0+ with MPU.
    let mut mpu = unsafe { Mpu::new(core_periph.MPU) };

    let mut regions = ArrayVec::new();
    let userapp_size = userapp_end() - userapp_start();
    assert!(userapp_size <= 1024);
    regions.push(Region {
        base_addr: userapp_start(),
        size: Size::S1K,
        executable: true,
        permissions: AccessPermission::ReadWrite,
        attributes: MEMATTR_FLASH,
    });
    regions.push(Region {
        base_addr: unsafe { DATA_READONLY.0.as_ptr() as usize },
        size: Size::S256B,
        executable: false,
        permissions: AccessPermission::ReadOnly,
        attributes: MEMATTR_RAM,
    });
    regions.push(Region {
        base_addr: unsafe { DATA_NOACCESS.0.as_ptr() as usize },
        size: Size::S256B,
        executable: false,
        permissions: AccessPermission::NoAccess,
        attributes: MEMATTR_RAM,
    });
    mpu.configure_unprivileged(&regions);

    // Write to stack memory
    let mut _stack = 0;
    _stack = 1;

    unsafe {
        // Privileged code should be able to read/write both arrays:
        let p = DATA_NOACCESS.0.as_mut_ptr();
        ptr::read_volatile::<u8>(p);
        ptr::write_volatile(p, 0xfe);

        let p = DATA_READONLY.0.as_mut_ptr();
        ptr::read_volatile::<u8>(p);
        ptr::write_volatile(p, 0xfe);
    }

    hprintln!(
        "user code at 0x{:08x}-0x{:08x}",
        userapp_start(),
        userapp_end()
    )
    .ok();
    hprintln!("MPU configured, going unprivileged").ok();

    run_user_code();
}

extern "C" {
    static __suserapp: u32;
    static __euserapp: u32;
}

fn userapp_start() -> usize {
    unsafe { &__suserapp as *const _ as _ }
}

fn userapp_end() -> usize {
    unsafe { &__euserapp as *const _ as _ }
}

/// Which test to perform in the user app code.
#[allow(dead_code)]
enum Test {
    /// Don't do anything that would cause an MPU fault.
    ///
    /// If this still causes a fault, something is wrong.
    None,

    /// Call a function that's located outside the `.userapp` section,
    Call,

    /// Read from a memory region mapped as inaccessible.
    ReadNoAccess,

    /// Write to a memory region mapped as read-only.
    WriteReadOnly,
}

const TEST: Test = Test::None;

#[link_section = ".userapp"]
#[inline(never)]
fn run_user_code() -> ! {
    enter_unprivileged();

    match TEST {
        Test::None => {}
        Test::Call => call_me_to_crash(),
        Test::ReadNoAccess => unsafe {
            let p = DATA_NOACCESS.0.as_ptr();
            ptr::read_volatile::<u8>(p as *const _);
        },
        Test::WriteReadOnly => unsafe {
            let p = DATA_READONLY.0.as_mut_ptr();
            ptr::write_volatile(p, 0xfe);
        },
    }

    loop {}
}

#[link_section = ".userapp"]
fn enter_unprivileged() {
    // This should use the cortex-m API once https://github.com/rust-embedded/cortex-m/pull/164
    // is merged (and released).
    // Note that that API cannot be used correctly in this context unless the `inline-asm` feature
    // is enabled (it already should be).
    unsafe {
        let control = control::read().bits() | 1;
        asm!("msr CONTROL, $0" :: "r"(control) : "memory" : "volatile");
    }
}

/// This isn't in the `.userapp` section, so it can not be accessed (read or executed) from
/// unprivileged code (since its memory region isn't in the MPU config).
#[inline(never)]
fn call_me_to_crash() {
    asm::nop();
}

#[repr(align(256))]
struct Aligned<T>(T);

/// The first half of this data will be set to readonly protection.
static mut DATA_READONLY: Aligned<&'static mut [u8]> = Aligned(&mut [0; 16]);

/// The first half of this data will be set to be completely inaccessible by the user code.
static mut DATA_NOACCESS: Aligned<&'static mut [u8]> = Aligned(&mut [0; 16]);
