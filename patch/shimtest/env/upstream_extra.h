/* shimtest only: forced include of the -DUPSTREAM build.  Kernel configuration as on x86_64 (IS_ENABLED with the
 * kconfig.h placeholder trick; CONFIG_HAVE_EFFICIENT_UNALIGNED_ACCESS and CONFIG_64BIT are set on the command
 * line), and the generic get/put_unaligned, OPTIMIZER_HIDE_VAR and __ffs the upstream files use. */
#include "quickproof_kernel.h"
#undef IS_ENABLED
#define __ARG_PLACEHOLDER_1 0,
#define __take_second_arg(__ignored, val, ...) val
#define __is_defined(x) ___is_defined(x)
#define ___is_defined(val) ____is_defined(__ARG_PLACEHOLDER_##val)
#define ____is_defined(arg1_or_junk) __take_second_arg(arg1_or_junk 1, 0)
#define IS_ENABLED(option) __is_defined(option)
#define get_unaligned(ptr) ({ __typeof__(*(ptr)) __v; __builtin_memcpy(&__v, (ptr), sizeof(__v)); __v; })
#define put_unaligned(val, ptr) ({ __typeof__(*(ptr)) __v = (val); __builtin_memcpy((ptr), &__v, sizeof(__v)); (void)0; })
#define OPTIMIZER_HIDE_VAR(var) __asm__ ("" : "=r" (var) : "0" (var))
#define __ffs(x) ((unsigned long)__builtin_ctzl(x))
