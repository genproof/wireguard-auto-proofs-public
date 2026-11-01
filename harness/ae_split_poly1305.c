// Law ae_split_poly1305: For any 32-byte key and any message (up to PTRDIFF_MAX bytes), poly1305_init,
// poly1305_update over the whole message and poly1305_final give the same 16-byte tag as poly1305_update over the
// message in any pieces of any lengths (empty pieces too).
#include "wg_laws.h"

int main(void) {
	// Choose the inputs: any key, any message
	u8 key[POLY1305_KEY_SIZE];
	nondet_bytes(key, sizeof key);
	size_t len = upto(PTRDIFF_MAX);
	u8 *message = any_bytes(len);
	if (message == NULL)
		return 0;
	// In one call
	struct poly1305_desc_ctx one, many;
	u8 whole[POLY1305_DIGEST_SIZE], pieces[POLY1305_DIGEST_SIZE];
	poly1305_init(&one, key);
	poly1305_update(&one, message, len);
	poly1305_final(&one, whole);
	// In any pieces. RFC 8439, 2.5.1: "divide the message into 16-byte blocks. The last one might be shorter":
	// the tag depends on the key and the message only, not on how the message was handed over.
	poly1305_init(&many, key);
	size_t done = 0;
	while (done < len || nondet_u8() != 0) {
		size_t take = upto(len - done);
		poly1305_update(&many, message + done, take);
		done += take;
	}
	poly1305_final(&many, pieces);
	// Check
	gp_assert(bytes_eq(whole, pieces, POLY1305_DIGEST_SIZE));
	return 0;
}
