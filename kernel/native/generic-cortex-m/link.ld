ENTRY(_start)

__OXIDE_SE_BOOT_ABI_SIZE = 0x20;

__StackLimit = ORIGIN(RAM);
__StackTop = __StackLimit + __STACK_SIZE_CPU0;
__oxide_se_boot_abi_start = __StackTop;
__fae_ram_start = __oxide_se_boot_abi_start + __OXIDE_SE_BOOT_ABI_SIZE;
__fae_ram_end = ORIGIN(RAM) + LENGTH(RAM);

SECTIONS
{
  . = ORIGIN(FLASH);

  ._start : ALIGN(4)
  {
    KEEP(*("._start"))
    . = ALIGN(4);
  } > FLASH

  .text : ALIGN(4)
  {
    *(.text .text.*)
    *(.rodata .rodata.*)
    . = ALIGN(4);
  } > FLASH

  .data __fae_ram_start : ALIGN(4)
  {
    __data_start = .;
    *(.data .data.*)
    . = ALIGN(4);
    __data_end = .;
  } > RAM AT > FLASH
  __data_load = LOADADDR(.data);

  .bss (NOLOAD) : ALIGN(4)
  {
    __bss_start = .;
    *(.bss .bss.*)
    *(COMMON)
    . = ALIGN(4);
    __bss_end = .;
  } > RAM

  __ram_end = ALIGN(8);

  /DISCARD/ :
  {
    *(.ARM.exidx*)
    *(.eh_frame*)
    *(.comment)
    *(.note*)
    *(.ARM.attributes)
  }
}

ASSERT(__fae_ram_end >= __fae_ram_start, "Invalid RAM window for native ELF")
ASSERT(__ram_end <= __fae_ram_end, "Native ELF RAM sections overflow target RAM")

/* Startup and exception assembly consume aligned words and an AAPCS stack. */
ASSERT(__STACK_SIZE_CPU0 > 0 && (__StackLimit % 8) == 0 && (__StackTop % 8) == 0,
       "Kernel stack must be nonempty and eight-byte aligned")
ASSERT(__OXIDE_SE_BOOT_ABI_SIZE == 32 && (__oxide_se_boot_abi_start % 4) == 0,
       "Exception forwarding ABI must contain eight aligned words")
ASSERT((__data_start % 4) == 0 && (__data_end % 4) == 0,
       "Startup data loop requires aligned whole words")
ASSERT((__bss_start % 4) == 0 && (__bss_end % 4) == 0,
       "Startup bss loop requires aligned whole words")
ASSERT((__data_load % 4) == 0, "Startup data source must be word aligned")
ASSERT(__data_end <= __bss_start, "Startup RAM sections must not overlap")
