/* SPDX-License-Identifier: GPL-2.0 */
/*
 * QUICKPROOF S18 SHIM for drivers/net/wireguard/timers.h: only wg_birthdate_has_expired, whose body is upstream's
 * (drivers/net/wireguard/timers.c at the pinned commit), in patch/wg_shim.c.
 */
#ifndef _WG_TIMERS_H
#define _WG_TIMERS_H
#include "quickproof_kernel.h"
bool wg_birthdate_has_expired(u64 birthday_nanoseconds, u64 expiration_seconds);
#endif
