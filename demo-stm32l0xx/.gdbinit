# disable "are you sure you want to quit?"
define hook-quit
    set confirm off
end

target extended-remote :2331

# print demangled symbols by default
set print asm-demangle on

monitor semihosting enable

load

monitor reset
cont
