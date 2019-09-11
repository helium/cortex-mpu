/*

Special linker script that ensures the user code section is aligned properly
and that we have information about its size.

*/

SECTIONS {
    .userapp : ALIGN(2048) {
        . = ALIGN(2048);
        __suserapp = .;  // place the __userapp symbol at the current address
        *(.userapp .userapp.*);
        . = ALIGN(2048);
        __euserapp = .;
    } > FLASH AT> FLASH
}
