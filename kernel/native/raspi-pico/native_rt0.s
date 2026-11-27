    .syntax unified
    .arch armv6s-m
    .thumb

    .include "kernel/native/raspi-pico/boot2_w25q080.S"

    .section .vectors, "ax", %progbits
    .align 2
    .global __Vectors
    .type __Vectors, %object
__Vectors:
    .word   __StackTop
    .word   Reset_Handler
    .word   Unexpected_Handler
    .word   HardFault_Handler
    .word   0
    .word   0
    .word   0
    .word   0
    .word   0
    .word   0
    .word   0
    .word   SVC_Handler
    .word   0
    .word   0
    .word   Unexpected_Handler
    .word   oxi_core_periodic_timer_interrupt_handler

board_name:
    .asciz "raspi-pico1: "

    .equ SCB_VTOR,        0xE000ED08
    .equ DBG_BASE,        0x5FFF0000
    .equ DBG_ARG0,        0x5FFF0004
    .equ DBG_CMD_EXIT,    0x54495845

    .global _start
    .thumb_set _start, Reset_Handler

    .align 2
    .thumb_func
Reset_Handler:
    cpsid   i
    ldr     r0, =__StackTop
    mov     sp, r0

    ldr     r0, =__Vectors
    ldr     r1, =SCB_VTOR
    str     r0, [r1]

    dsb
    isb
    /* Linker-reserved ABI storage is outside .bss: clear stale handlers on
     * every reset. Runtime initialization publishes them before IRQ enable. */
    ldr     r0, =__oxide_se_boot_abi_start
    ldr     r1, =__fae_ram_start
    movs    r2, #0
.Lclear_boot_abi:
    cmp     r0, r1
    bcs     .Lboot_abi_cleared
    str     r2, [r0]
    adds    r0, #4
    b       .Lclear_boot_abi
.Lboot_abi_cleared:

    bl      copy_critical_kernel_fct
    bl      copy_data
    bl      zero_bss
    bl      start

    movs    r0, #0
    b       die_common

    .thumb_func
SVC_Handler:
    ldr     r0, =oxi_core_armv6m_svcall_handler
    movs    r1, #1
    orrs    r0, r1
    bx      r0

    .thumb_func
HardFault_Handler:
    ldr     r0, =oxi_core_armv6m_hardfault_handler
    movs    r1, #1
    orrs    r0, r1
    bx      r0

    .thumb_func
Unexpected_Handler:
    ldr     r0, =__StackTop
    mov     sp, r0
    bkpt    #0
1:
    b       1b

die_common:
    ldr     r1, =DBG_ARG0
    str     r0, [r1]
    ldr     r1, =DBG_BASE
    ldr     r2, =DBG_CMD_EXIT
    str     r2, [r1]
1:
    b       1b

    .thumb_func
copy_critical_kernel_fct:
    ldr     r0, =__critical_kernel_fct_load
    ldr     r1, =__critical_kernel_fct_start
    ldr     r2, =__critical_kernel_fct_end
copy_critical_kernel_fct_loop:
    cmp     r1, r2
    bcs     copy_critical_kernel_fct_done
    ldr     r3, [r0]
    str     r3, [r1]
    adds    r0, #4
    adds    r1, #4
    b       copy_critical_kernel_fct_loop
copy_critical_kernel_fct_done:
    bx      lr

    .thumb_func
copy_data:
    ldr     r0, =__data_load
    ldr     r1, =__data_start
    ldr     r2, =__data_end
copy_data_loop:
    cmp     r1, r2
    bcs     copy_data_done
    ldr     r3, [r0]
    str     r3, [r1]
    adds    r0, #4
    adds    r1, #4
    b       copy_data_loop
copy_data_done:
    bx      lr

    .thumb_func
zero_bss:
    ldr     r0, =__bss_start
    ldr     r1, =__bss_end
    movs    r2, #0
zero_bss_loop:
    cmp     r0, r1
    bcs     zero_bss_done
    str     r2, [r0]
    adds    r0, #4
    b       zero_bss_loop
zero_bss_done:
    bx      lr
