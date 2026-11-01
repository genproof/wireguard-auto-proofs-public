// SPDX-License-Identifier: GPL-2.0
// Law `replay`: replayed and non-newer initiations are rejected, over ANY sequence of initiations.
//
// Devices A and B with ANY static keys and one preshared key (or none), each with a peer for the other.
// A sequence of ANY length of events, each one of:
//   - A creates a new initiation (any real-time clock, which may go backwards; any ephemeral randomness), adds
//     its macs, and B consumes it;
//   - B consumes again the last initiation A created (a replay, possibly of a rejected one);
//   - B consumes again the last initiation it accepted (a replay of an accepted one);
// with B's boot clock moving forward by ANY amount (possibly 0) before each consumption.
// Claims, against a shadow model of B's view of A (latest accepted TAI64N timestamp, last consumption time):
//  - B accepts exactly when the message decrypts (model) AND its timestamp is greater than every timestamp
//    accepted so far AND the last acceptance was at least 20 ms ago; the accepted initiation updates the model;
//  - a replay of an accepted initiation is ALWAYS rejected;
//  - a rejected initiation changes nothing in B's handshake (byte for byte) nor its peer's references;
//  - peer references are balanced after every step.
#include "common.h"

static int copy_init(struct message_handshake_initiation *d, const struct message_handshake_initiation *s)
{
	d->header.type = s->header.type;
	d->sender_index = s->sender_index;
	bytes_copy(d->unencrypted_ephemeral, s->unencrypted_ephemeral, 32);
	bytes_copy(d->encrypted_static, s->encrypted_static, 48);
	bytes_copy(d->encrypted_timestamp, s->encrypted_timestamp, 28);
	bytes_copy(d->macs.mac1, s->macs.mac1, 16);
	bytes_copy(d->macs.mac2, s->macs.mac2, 16);
	return 1;
}

int main(void)
{
	struct wg_device wa, wb;
	struct index_hashtable ita, itb;
	struct pubkey_hashtable pta, ptb;
	struct wg_peer pa, pb;
	struct m_identity ia, ib;
	u8 raw_a[32], raw_b[32], psk[32], ss_b[32], latest[12];
	struct message_handshake_initiation *sent, *accepted, *m;
	struct m_consumed_initiation ci;
	struct hs_snap snap;
	struct wg_peer *ret;
	int have_sent = 0, have_accepted = 0, use_psk, kind, acc;
	size_t steps, i;
	u64 now, last;

	wg_shim_boottime_ns = draw_boottime();
	wg_noise_init();
	nondet_bytes(raw_a, 32);
	nondet_bytes(raw_b, 32);
	use_psk = nondet_u8() & 1;
	nondet_bytes(psk, 32);
	setup_device(&wa, &ita, &pta, raw_a);
	setup_device(&wb, &itb, &ptb, raw_b);
	m_identity_of(&ia, raw_a);
	m_identity_of(&ib, raw_b);
	setup_peer(&pb, &wa, ib.pub, use_psk ? psk : NULL, 1);
	setup_peer(&pa, &wb, ia.pub, use_psk ? psk : NULL, 2);
	m_precomputed(ss_b, &ib, ia.pub);

	sent = malloc(sizeof(*sent));
	accepted = malloc(sizeof(*accepted));
	m = malloc(sizeof(*m));
	if (sent == NULL || accepted == NULL || m == NULL) {
		free(sent);
		free(accepted);
		free(m);
		return 0;
	}
	bytes_set(latest, 0, 12);   // the shadow model: nothing accepted yet
	last = 0;
	now = draw_boottime();

	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		kind = nondet_u8() % 3;
		if (kind == 0) {
			fill_init(m);
			draw_real_clock();
			if (!wg_noise_handshake_create_initiation(m, &pb.handshake))
				continue;   // (A has no identity, or a zero DH: law create_any)
			wg_cookie_add_mac_to_packet(m, sizeof(*m), &pb);
			copy_init(sent, m);
			have_sent = 1;
		} else if (kind == 1) {
			if (!have_sent)
				continue;
			copy_init(m, sent);
		} else {
			if (!have_accepted)
				continue;
			copy_init(m, accepted);
		}
		// B's clock moves forward by any amount (staying below 2^62)
		{
			u64 d = draw_u64() >> (nondet_u8() % 64);
			if (d < ((1ULL << 62) - now))
				now += d;
		}
		wg_shim_boottime_ns = now;
		hs_take(&snap, &pa.handshake);
		ret = wg_noise_handshake_consume_initiation(m, &wb);
		acc = ib.ok && m_consume_initiation_1(&ci, &ib, m->unencrypted_ephemeral, m->encrypted_static) &&
		      bytes_eq(ci.spub, ia.pub, 32) && m_consume_initiation_2(&ci, ss_b, m->encrypted_timestamp) &&
		      m_ts_newer(ci.ts, latest) && m_not_flood(last, now);
		if (kind == 2)
			CHECK(!acc);   // the model never accepts a replay of an accepted initiation
		if (!acc) {
			CHECK(ret == NULL && hs_same(&snap, &pa.handshake) && pa.refcount.refcount == 1);
		} else {
			CHECK(ret == &pa && pa.refcount.refcount == 2);
			wg_peer_put(ret);
			CHECK(pa.refcount.refcount == 1);
			CHECK(pa.handshake.state == HANDSHAKE_CONSUMED_INITIATION);
			CHECK(bytes_eq(pa.handshake.latest_timestamp, ci.ts, 12));
			CHECK(pa.handshake.last_initiation_consumption == m_last_consumption(last, now));
			CHECK(bytes_eq(pa.handshake.hash, ci.st.h, 32) && bytes_eq(pa.handshake.chaining_key, ci.st.ck, 32));
			bytes_copy(latest, ci.ts, 12);
			last = m_last_consumption(last, now);
			copy_init(accepted, m);
			have_accepted = 1;
		}
	}
	free(sent);
	free(accepted);
	free(m);
	return 0;
}
