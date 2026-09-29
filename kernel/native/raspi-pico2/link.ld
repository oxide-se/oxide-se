ENTRY(_start)

__OXIDE_SE_BOOT_ABI_SIZE = 0x20;

__StackLimit = ORIGIN(RAM);
__StackTop = __StackLimit + __STACK_SIZE_CPU0;
__oxide_se_boot_abi_start = __StackTop;
__fae_ram_start = __oxide_se_boot_abi_start + __OXIDE_SE_BOOT_ABI_SIZE;
__oxide_se_kernel_mutable_ram_start = ORIGIN(RAM);
/* Keep RAM-executed flash primitives outside the allocator and NX window. */
__oxide_se_kernel_mutable_ram_size = LENGTH(RAM) - 0x4000;
__oxide_se_kernel_mutable_ram_end = __oxide_se_kernel_mutable_ram_start + __oxide_se_kernel_mutable_ram_size;
__oxide_se_critical_kernel_fct_ram_start = __oxide_se_kernel_mutable_ram_start + __oxide_se_kernel_mutable_ram_size;
__fae_ram_end = ORIGIN(RAM) + LENGTH(RAM);

__registry_persistence_page_size = 0x100;
__registry_persistence_erase_sector_size = 0x1000;
__registry_persistence_page_count = 1024;
__registry_persistence_size = __registry_persistence_page_size * __registry_persistence_page_count;
__registry_persistence_end = ORIGIN(FLASH) + LENGTH(FLASH);
__registry_persistence_start = __registry_persistence_end - __registry_persistence_size;

SECTIONS
{
  . = ORIGIN(FLASH);

  .vectors : ALIGN(4) 
  {
    KEEP(*(.vectors)) /* Size: 0x7c0*/
    KEEP(*(.picobin_block))
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

  .critical.kernel.fct __oxide_se_critical_kernel_fct_ram_start : ALIGN(4)
  {
    __critical_kernel_fct_start = .;
    KEEP(*(.critical.kernel.fct .critical.kernel.fct.*))
    KEEP(*(.text.*p256*))
    KEEP(*(.text.*elliptic_curve*))
    KEEP(*(.text.*crypto_bigint*))
    KEEP(*(.text.*primeorder*))
    KEEP(*(.text.*sec1*))
    KEEP(*(.text.*subtle*))
    KEEP(*(.text.*_2ff*))
    . = ALIGN(4);
    __critical_kernel_fct_end = .;
  } > RAM AT > FLASH
  

  __critical_kernel_fct_load = LOADADDR(.critical.kernel.fct);

  __flash_image_end = LOADADDR(.critical.kernel.fct) + SIZEOF(.critical.kernel.fct);

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
ASSERT(__ram_end <= __oxide_se_kernel_mutable_ram_end, "Native ELF mutable RAM sections overflow the Pico kernel RAM-XN window")
ASSERT(__ram_end <= __fae_ram_end, "Native ELF RAM sections overflow target RAM")
ASSERT(__critical_kernel_fct_end <= __fae_ram_end, "Pico2 RAM-executable code exceeds its reserved 16 KiB")
ASSERT(__registry_persistence_start % __registry_persistence_page_size == 0, "Registry persistence start must be page-aligned")
ASSERT(__registry_persistence_start % __registry_persistence_erase_sector_size == 0, "Registry persistence start must be erase-sector-aligned")
ASSERT(__flash_image_end <= __registry_persistence_start, "Native ELF flash image overlaps registry persistence area")

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
ASSERT((__critical_kernel_fct_load % 4) == 0 &&
       (__critical_kernel_fct_start % 4) == 0 && (__critical_kernel_fct_end % 4) == 0,
       "RAM code relocation requires aligned whole words")
ASSERT(__ram_end <= __critical_kernel_fct_start && __critical_kernel_fct_end <= __fae_ram_end,
       "RAM code must remain outside mutable data and inside target RAM")
