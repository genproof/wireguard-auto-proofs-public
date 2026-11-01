// SPDX-License-Identifier: GPL-2.0
/*
 * data_header.c: the length validation of drivers/net/wireguard/receive.c (validate_header_len), extracted as a
 * REDUCTION for the law transport_len.  Copyright (C) 2015-2019 Jason A. Donenfeld <Jason@zx2c4.com>.
 *
 * QUICKPROOF S24 (DEVIATIONS.md): NOT byte for byte, unlike patch/counter_validate.c (S19).  The function between
 * the markers is upstream's text at the pinned commit with exactly three substitutions, which patch/wgpatch.py
 * checks against receive.c at the pin (patch/check.sh fails if the pin and this text diverge):
 *   the signature  `static size_t validate_header_len(struct sk_buff *skb)`
 *              ->  `size_t wg_validate_header_len(u32 type, size_t len)`  (non-static, callable by a harness);
 *   `SKB_TYPE_LE32(skb)` -> `type`   (the packet's type word, ((struct message_header *)skb->data)->type);
 *   `skb->len`           -> `len`    (the packet's length).
 * The two skb accessors become parameters because the sk_buff machinery around them is not modelled.  Every length branch and every constant (sizeof(struct message_header /
 * message_data / ...), MESSAGE_MINIMUM_LENGTH) is upstream's.  Returns the header length (0 = reject), exactly as
 * validate_header_len does.  The rest of receive.c is not compiled.
 */
#include "quickproof_kernel.h"
#include "noise.h"
#include "messages.h"

size_t wg_validate_header_len(u32 type, size_t len);

/* ---- BEGIN REDUCED receive.c ---- */
size_t wg_validate_header_len(u32 type, size_t len)
{
	if (unlikely(len < sizeof(struct message_header)))
		return 0;
	if (type == cpu_to_le32(MESSAGE_DATA) &&
	    len >= MESSAGE_MINIMUM_LENGTH)
		return sizeof(struct message_data);
	if (type == cpu_to_le32(MESSAGE_HANDSHAKE_INITIATION) &&
	    len == sizeof(struct message_handshake_initiation))
		return sizeof(struct message_handshake_initiation);
	if (type == cpu_to_le32(MESSAGE_HANDSHAKE_RESPONSE) &&
	    len == sizeof(struct message_handshake_response))
		return sizeof(struct message_handshake_response);
	if (type == cpu_to_le32(MESSAGE_HANDSHAKE_COOKIE) &&
	    len == sizeof(struct message_handshake_cookie))
		return sizeof(struct message_handshake_cookie);
	return 0;
}
/* ---- END REDUCED receive.c ---- */
