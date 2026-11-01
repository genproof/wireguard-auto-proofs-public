// SPDX-License-Identifier: GPL-2.0
// Law `handshake_receive`: the receive side of the handshake gates the consume functions exactly as
// the protocol requires, over ANY sequence of packets of ANY bytes and ANY length.  Code under test besides the
// units: receive.c's validate_header_len and wg_receive_handshake_packet, extracted byte for byte
// (patch/receive_handshake.c, compiled into this harness only; its calls to send.c / socket.c / timers.c are a
// recording shim: DEVIATIONS.md S22, S23).
//
// State: device D with ANY static key, ANY cookie secret and secret age; ANY number of peers (unique public keys)
// with ANY handshake state (common.h hs_randomize) and other state (peer_randomize_rest), any reference count below
// INT_MAX (common.h draw_peer_refs), entries hashed or not, ANY number of keypairs (whole objects of ANY content,
// common.h kents_add; not in the slots, which begin_session rotates) of ANY peers in the table; one peer K whose
// private key the harness knows. A sequence of ANY length of packets, with the boot clock moving forward by any
// amount, ANY handshake-queue length (the load), ANY rate-limiter answer and ANY source address/port, each packet
// one of: ANY bytes of ANY length (other than 148, 92, 64; possibly beginning with K's initiation or response, i.e.
// with bytes after a valid message; the type word drawn, or set to 1..4 with or without nonzero reserved bytes; the
// last 32 bytes possibly a correct mac1 / mac2 of the rest); 148 bytes with ANY fields or K's initiation to D (the
// model's); 92 bytes with ANY fields or K's response to D's current handshake with K (the model's); 64 bytes with
// ANY fields (receiver index drawn or one of the table's) or a cookie reply that decrypts for any peer that sent a
// mac1; the type word exact, with nonzero reserved bytes, or any; mac1 the correct one (D's mac1 key) or any; mac2
// the correct one for D's current cookie of the source, zero or any.  The harness hands a packet to
// wg_receive_handshake_packet as wg_packet_receive does: when validate_header_len accepts it and its type word is 1,
// 2 or 3 (receive.c's UDP/IP parsing and the handshake queue are not covered: DEVIATIONS.md L14).
// Claims, for every packet (the model: whitepaper 5.3 / 5.4 and receive.c's load logic):
//  - unless the type word is exactly 1, 2 or 3 (reserved bytes zero) and the length exactly 148, 92 or 64
//    accordingly, NOTHING changes: every peer as a whole, the device (cookie secret included), the index table;
//    nothing is allocated; no call leaves the verified units (a message of type 1 / 2 / 3 with nonzero reserved
//    bytes, or of a length that is not exact - also with valid content followed by extra bytes - is dropped);
//  - a cookie reply (type 3): exactly law cookie_reply's acceptance and update, nothing else, no call;
//  - an initiation or response (type 1 / 2): D is "under load" when the queue holds at least
//    MAX_QUEUED_INCOMING_HANDSHAKES / 8 = 512 packets (then last_under_load = now), or else when it last was less
//    than 1 s ago, exactly as receive.c decides it: still under load iff NOT (s64)(last_under_load + 1 s) <=
//    (s64)now, so exactly 1 s after the last overload D is no longer under load (and last_under_load is reset to
//    0) - modelled across the sequence; the verdict on mac1 / mac2 is law cookie_mac's model, with the cookie
//    secret replaced by a fresh random one when (s64)(secret birthdate + 120 s) <= (s64)now, i.e. at EXACTLY
//    120 s (wireguard-go: only after 120 s); then
//      * no valid mac1, or valid macs but rate limited: NOTHING changes but that rotation, no call;
//      * under load without a valid mac2: exactly one cookie reply is sent, for the message's sender index, and
//        nothing else changes (no consume);
//      * otherwise the consume function runs and the result is exactly the model's (laws consume_initiation_any,
//        consume_response_any: identity, DH, decryption, known peer, timestamp newer, at least 20 ms since the
//        last initiation - accepted at exactly 20 ms -, state CREATED_INITIATION, tag): rejected -> NOTHING
//        changes, no call; accepted (peer P) -> P's handshake is the model's (an initiation: CONSUMED_INITIATION
//        with the model's hash, chaining key, remote ephemeral, timestamp, indices; a response: the session begins,
//        begin_session zeroing it and, unless the allocation fails or P is dead, moving its index to the new current
//        keypair), the endpoint is set from THIS packet, a response is sent (initiation) or, if a session was made,
//        the session timers run and a keepalive is sent (response), the rx statistics get the packet's length,
//        both authenticated-packet timers run - each exactly once, all for P; every other peer unchanged;
//        references balanced; nothing allocated but the keypair; no reference count saturates or warns;
//  - the packet is never modified.
// (After a session is made the harness clears P's keypairs, so that every packet starts from a state of the same
// shape; law keypairs covers what sessions do.  The harness draws the boundaries on purpose: queue lengths
// 510..514, the clock exactly 1 s +- 2 ns after the last overload, 120 s +- 2 ns after the cookie secret's birth,
// 20 ms +- 2 ns after K's last initiation.)
#include "common.h"
#include "../patch/receive_handshake.c"

static int m_expired(u64 birthdate, u64 seconds, u64 now)
{
	return (s64)(birthdate + seconds * 1000000000ULL) <= (s64)now;
}

static void m_cookie(u8 out[16], const u8 secret[32], const struct sk_buff *skb)
{
	u8 buf[18];
	size_t n = 0;
	if (skb->protocol == htons(ETH_P_IP)) {
		bytes_copy(buf, skb->ip4.saddr.s_addr, 4);
		n = 4;
	} else if (skb->protocol == htons(ETH_P_IPV6)) {
		bytes_copy(buf, skb->ip6.saddr.s6_addr, 16);
		n = 16;
	}
	bytes_copy(buf + n, skb->udp.source, 2);
	m_mac(out, secret, 32, buf, n + 2);
}

static void rx_reset(void)
{
	wg_shim_rx.cookie = 0;
	wg_shim_rx.cookie_index = 0;
	wg_shim_rx.endpoint = 0;
	wg_shim_rx.endpoint_skb = NULL;
	wg_shim_rx.response = 0;
	wg_shim_rx.session_derived = 0;
	wg_shim_rx.handshake_complete = 0;
	wg_shim_rx.keepalive = 0;
	wg_shim_rx.rx_stats = 0;
	wg_shim_rx.rx_len = 0;
	wg_shim_rx.received = 0;
	wg_shim_rx.traversal = 0;
	wg_shim_rx.peer = NULL;
	wg_shim_rx.other_peer = false;
}

// no call left the verified units, but (cookie = 1) the cookie reply
static int rx_only_cookie(unsigned int cookie)
{
	return wg_shim_rx.cookie == cookie && wg_shim_rx.endpoint == 0 && wg_shim_rx.response == 0 &&
	       wg_shim_rx.session_derived == 0 && wg_shim_rx.handshake_complete == 0 && wg_shim_rx.keepalive == 0 &&
	       wg_shim_rx.rx_stats == 0 && wg_shim_rx.received == 0 && wg_shim_rx.traversal == 0 &&
	       wg_shim_rx.peer == NULL && !wg_shim_rx.other_peer;
}

// the calls of an authenticated handshake message from peer p
static int rx_authenticated(struct wg_peer *p, const struct sk_buff *skb, unsigned int response, unsigned int session)
{
	return wg_shim_rx.cookie == 0 && wg_shim_rx.endpoint == 1 && wg_shim_rx.endpoint_skb == skb &&
	       wg_shim_rx.response == response && wg_shim_rx.session_derived == session &&
	       wg_shim_rx.handshake_complete == session && wg_shim_rx.keepalive == session &&
	       wg_shim_rx.rx_stats == 1 && wg_shim_rx.rx_len == skb->len && wg_shim_rx.received == 1 &&
	       wg_shim_rx.traversal == 1 && wg_shim_rx.peer == p && !wg_shim_rx.other_peer;
}

// how wg_packet_receive hands a packet to the handshake worker (prepare_skb_header's validate_header_len, then the
// type switch); the queue in between is not modelled (L14)
static void dispatch(struct wg_device *wg, struct sk_buff *skb)
{
	if (validate_header_len(skb) == 0)
		return;
	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_INITIATION) ||
	    SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_RESPONSE) ||
	    SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_COOKIE))
		wg_receive_handshake_packet(wg, skb);
}

// the type word: exact, with nonzero reserved bytes, or any
static u32 draw_type(u32 t)
{
	switch (nondet_u8() % 4) {
	case 0: return t | ((u32)(1 + nondet_u8() % 255) << (8 * (1 + nondet_u8() % 3)));
	case 1: return nondet_u32();
	default: break;
	}
	return t;
}

// K's initiation to D, as the model builds it (any ephemeral randomness, any real-time clock); the other fields as
// they are
static void k_initiation(struct message_handshake_initiation *m, const struct m_identity *ik,
			 const struct m_identity *id, const u8 ss_k[32])
{
	struct m_initiation mi;
	u8 eraw[32], ts[12];
	nondet_bytes(eraw, 32);
	draw_real_clock();
	m_tai64n(ts, wg_shim_real_sec, wg_shim_real_nsec);
	if (m_create_initiation(&mi, ik->pub, id->pub, ss_k, eraw, ts)) {
		bytes_copy(m->unencrypted_ephemeral, mi.ephemeral, 32);
		bytes_copy(m->encrypted_static, mi.enc_static, 48);
		bytes_copy(m->encrypted_timestamp, mi.enc_timestamp, 28);
	}
}

// K's response to D's current handshake with K, as the model builds it (any responder ephemeral); sometimes K's
// handshake is first made one that waits for a response (state CREATED_INITIATION, in the table)
static void k_response(struct message_handshake_response *m, struct noise_handshake *h, struct index_hashtable *t,
		       const struct m_identity *id)
{
	struct m_response mr;
	struct m_state cur;
	u8 eraw[32], ei[32];
	if (nondet_u8() & 1) {
		h->state = HANDSHAKE_CREATED_INITIATION;
		if (!h->entry.hashed)
			wg_index_hashtable_insert(t, &h->entry);
	}
	nondet_bytes(eraw, 32);
	bytes_copy(cur.ck, h->chaining_key, 32);
	bytes_copy(cur.h, h->hash, 32);
	m_dh(ei, h->ephemeral_private, M_BASEPOINT);
	if (m_create_response(&mr, &cur, ei, id->pub, h->preshared_key, eraw)) {
		m->receiver_index = h->entry.index;
		bytes_copy(m->unencrypted_ephemeral, mr.ephemeral, 32);
		bytes_copy(m->encrypted_nothing, mr.enc_nothing, 16);
	}
}

// the last 32 bytes of a packet image (len >= 32): mac1 correct (D's mac1 key mk1) or as it is; mac2 correct (D's
// current cookie of the source), zero or as it is
static void draw_macs(u8 *img, size_t len, const u8 mk1[32], const u8 secret[32], const struct sk_buff *skb)
{
	u8 c[16], mac[16];
	if (nondet_u8() % 4 != 0) {
		m_mac(mac, mk1, 32, img, len - 32);
		bytes_copy(img + len - 32, mac, 16);
	}
	switch (nondet_u8() % 3) {
	case 0:
		m_cookie(c, secret, skb);
		m_mac(mac, c, 16, img, len - 16);
		bytes_copy(img + len - 16, mac, 16);
		break;
	case 1:
		bytes_set(img + len - 16, 0, 16);
		break;
	default:
		break;
	}
}

int main(void)
{
	struct wg_device wd;
	struct index_hashtable itd;
	struct pubkey_hashtable ptd;
	struct m_identity id, ik;
	u8 raw_d[32], raw_k[32], pub[32], mk1[32], ss_k[32];
	struct hnode *peers = NULL, *nk, *nd;
	struct kent *kes;
	struct dev_snap ds;
	struct shim_snap ss;
	struct skb_snap sks;
	struct index_hashtable_entry *head0, *e;
	struct sk_buff skb;
	size_t steps, i, n;
	u64 now, m_lul = 0;

	now = draw_boottime();
	wg_shim_boottime_ns = now;
	wg_noise_init();
	nondet_bytes(raw_d, 32);
	nondet_bytes(raw_k, 32);
	setup_device(&wd, &itd, &ptd, raw_d);
	m_identity_of(&id, raw_d);
	m_identity_of(&ik, raw_k);
	m_precomputed(ss_k, &ik, id.pub);   // K's precomputed DH with D
	if (id.ok)
		m_label_key(mk1, M_LABEL_MAC1, id.pub);   // D's mac1 key (law cookie_mac)
	else
		bytes_set(mk1, 0, 32);
	nondet_bytes(wd.cookie_checker.secret, 32);
	wd.cookie_checker.secret_birthdate = draw_boottime();
	nk = hnodes_add(&peers, &wd, ik.pub, 0);
	n = draw_steps();
	for (i = 0; i < n; i++) {
		nondet_bytes(pub, 32);
		hnodes_add(&peers, &wd, pub, 1 + i);
	}
	for (nd = peers; nd; nd = nd->next) {
		hs_randomize(&nd->p->handshake);
		peer_randomize_rest(nd->p);
		if (nondet_u8() % 4 != 0)
			wg_index_hashtable_insert(&itd, &nd->p->handshake.entry);
	}
	kes = kents_add(&itd, peers, NULL, 0);   // not in slots: begin_session rotates the slots

	steps = draw_steps();
	for (i = 0; i < steps; i++) {
		struct message_handshake_initiation *mi = NULL;
		struct message_handshake_response *mr = NULL;
		struct message_handshake_cookie *mc = NULL;
		u8 *buf = NULL, *img;
		size_t len;
		u32 tw;
		int kind, fwd, ul, verdict, path, rotated, acc_init = 0, acc_resp = 0;
		struct hnode *target = NULL;
		struct m_consumed_initiation ci;
		struct m_state st;
		u8 secret[32], c[16], mac[16], pt[16];
		u64 secret_birth;

		// the clock moves forward; the load, the rate limiter and the source: any
		{
			u64 d = draw_u64() >> (nondet_u8() % 64);
			if (d < ((1ULL << 62) - now))
				now += d;
		}
		if (nk != NULL && nondet_u8() % 8 == 0) {
			// the 20 ms flood limit's edge for K
			u64 edge = nk->p->handshake.last_initiation_consumption + 20000000 - 2 + nondet_u8() % 5;
			if (edge >= now && edge < (1ULL << 62))
				now = edge;
		}
		if (nondet_u8() % 8 == 0) {
			// the edge of the cookie secret's 120 s lifetime (cookie.c: wg_birthdate_has_expired(birthdate, 120))
			u64 edge = wd.cookie_checker.secret_birthdate + 120000000000ULL - 2 + nondet_u8() % 5;
			if (edge >= now && edge < (1ULL << 62))
				now = edge;
		}
		if (m_lul != 0 && nondet_u8() % 8 == 0) {
			// the edge of the 1 s under-load window (receive.c: wg_birthdate_has_expired(last_under_load, 1))
			u64 edge = m_lul + 1000000000ULL - 2 + nondet_u8() % 5;
			if (edge >= now && edge < (1ULL << 62))
				now = edge;
		}
		wg_shim_boottime_ns = now;
		// the queue length: any count (>= 0; the kernel's atomic_t counts queued packets).  A negative value would
		// make gcc and CompCert disagree: the enumeration constant MAX_QUEUED_INCOMING_HANDSHAKES is unsigned long
		// in gcc (its enum holds U64_MAX - ...) and int in CompCert (DEVIATIONS.md C04)
		switch (nondet_u8() % 4) {
		case 0: wg_shim_handshake_queue_len = 510 + nondet_u8() % 5; break;   // the load threshold's edge
		case 1: wg_shim_handshake_queue_len = (int)(nondet_u32() % 2048); break;
		default: wg_shim_handshake_queue_len = (int)(nondet_u32() & 0x7fffffffu); break;
		}
		wg_shim_ratelimit_allow = nondet_u8() & 1;
		switch (nondet_u8() % 3) {
		case 0: skb.protocol = htons(ETH_P_IP); break;
		case 1: skb.protocol = htons(ETH_P_IPV6); break;
		default: skb.protocol = (__be16)nondet_u32(); break;
		}
		nondet_bytes(skb.ip4.saddr.s_addr, 4);
		nondet_bytes(skb.ip6.saddr.s6_addr, 16);
		nondet_bytes(skb.udp.source, 2);

		// the packet
		kind = nondet_u8() % 4;
		if (kind == 0) {
			len = draw_size();
			if (len == INIT_LEN || len == RESP_LEN || len == COOKIE_MSG_LEN)
				len++;
			if (len > 0xffffffffu)
				continue;
			buf = malloc(len);
			if (buf == NULL)
				continue;
			nondet_bytes(buf, len);
			if (nk != NULL && len > INIT_LEN && nondet_u8() % 4 == 0) {
				// K's initiation with bytes after it (a length check that is not exact would accept it)
				struct message_handshake_initiation t;
				fill_init(&t);
				k_initiation(&t, &ik, &id, ss_k);
				t.header.type = MESSAGE_HANDSHAKE_INITIATION;
				init_img(buf, &t);
			} else if (nk != NULL && len > RESP_LEN && nondet_u8() % 4 == 0) {
				struct message_handshake_response t;
				fill_resp(&t);
				k_response(&t, &nk->p->handshake, &itd, &id);
				t.header.type = MESSAGE_HANDSHAKE_RESPONSE;
				resp_img(buf, &t);
			}
			if (len >= 4 && (nondet_u8() & 1))
				le32_store(buf, draw_type(1 + nondet_u8() % 4));
			if (len >= 32 && (nondet_u8() & 1))
				draw_macs(buf, len, mk1, wd.cookie_checker.secret, &skb);
			img = malloc(len);
			if (img == NULL) {
				free(buf);
				continue;
			}
			bytes_copy(img, buf, len);
			skb.data = buf;
		} else if (kind == 1) {
			mi = malloc(sizeof(*mi));
			img = malloc(INIT_LEN);
			if (mi == NULL || img == NULL) {
				free(mi);
				free(img);
				continue;
			}
			len = INIT_LEN;
			fill_init(mi);
			if (nk != NULL && (nondet_u8() & 1))
				k_initiation(mi, &ik, &id, ss_k);
			mi->header.type = draw_type(MESSAGE_HANDSHAKE_INITIATION);
			init_img(img, mi);
			draw_macs(img, len, mk1, wd.cookie_checker.secret, &skb);
			bytes_copy(mi->macs.mac1, img + len - 32, 16);
			bytes_copy(mi->macs.mac2, img + len - 16, 16);
			skb.data = (u8 *)mi;
		} else if (kind == 2) {
			mr = malloc(sizeof(*mr));
			img = malloc(RESP_LEN);
			if (mr == NULL || img == NULL) {
				free(mr);
				free(img);
				continue;
			}
			len = RESP_LEN;
			fill_resp(mr);
			if (nk != NULL && (nondet_u8() & 1))
				k_response(mr, &nk->p->handshake, &itd, &id);
			mr->header.type = draw_type(MESSAGE_HANDSHAKE_RESPONSE);
			resp_img(img, mr);
			draw_macs(img, len, mk1, wd.cookie_checker.secret, &skb);
			bytes_copy(mr->macs.mac1, img + len - 32, 16);
			bytes_copy(mr->macs.mac2, img + len - 16, 16);
			skb.data = (u8 *)mr;
		} else {
			mc = malloc(sizeof(*mc));
			img = malloc(COOKIE_MSG_LEN);
			if (mc == NULL || img == NULL) {
				free(mc);
				free(img);
				continue;
			}
			len = COOKIE_MSG_LEN;
			fill_cookie_msg(mc);
			if (itd.head != NULL && (nondet_u8() & 1)) {
				size_t k = nondet_size();
				for (e = itd.head; e->next != NULL && k > 0; e = e->next)
					k--;
				mc->receiver_index = e->index;
			}
			if (peers != NULL && (nondet_u8() & 1)) {
				// a cookie reply that decrypts for any peer X that sent a mac1 (as X's responder would make it)
				struct hnode *x = hnodes_pick(peers);
				struct noise_handshake *h = &x->p->handshake;
				u8 ck[16];
				if (!h->entry.hashed)
					wg_index_hashtable_insert(&itd, &h->entry);
				mc->receiver_index = h->entry.index;
				x->p->latest_cookie.have_sent_mac1 = true;
				nondet_bytes(ck, 16);
				xchacha20poly1305_encrypt(mc->encrypted_cookie, ck, 16, x->p->latest_cookie.last_mac1_sent, 16,
							  mc->nonce, x->p->latest_cookie.cookie_decryption_key);
			}
			mc->header.type = draw_type(MESSAGE_HANDSHAKE_COOKIE);
			cookie_img(img, mc);
			skb.data = (u8 *)mc;
		}
		skb.len = (unsigned int)len;

		// the model's forwarding, and the consume functions' verdicts (on the state before the packet)
		tw = len >= 4 ? le32_load(img) : 0;
		fwd = (tw == MESSAGE_HANDSHAKE_INITIATION && len == INIT_LEN) ||
		      (tw == MESSAGE_HANDSHAKE_RESPONSE && len == RESP_LEN) ||
		      (tw == MESSAGE_HANDSHAKE_COOKIE && len == COOKIE_MSG_LEN);
		hnodes_snap(peers);
		kents_snap(kes);
		if (fwd && kind == 1 && id.ok &&
		    m_consume_initiation_1(&ci, &id, mi->unencrypted_ephemeral, mi->encrypted_static)) {
			for (nd = peers; nd; nd = nd->next)
				if (target == NULL && bytes_eq(nd->p->handshake.remote_static, ci.spub, 32))
					target = nd;
			if (target != NULL) {
				u8 sst[32];
				m_precomputed(sst, &id, target->p->handshake.remote_static);
				acc_init = m_consume_initiation_2(&ci, sst, mi->encrypted_timestamp) &&
					   m_ts_newer(ci.ts, target->snap.latest_timestamp) &&
					   m_not_flood(target->snap.last_initiation_consumption, now);
			}
		} else if (fwd && kind == 2 && id.ok) {
			for (e = itd.head; e != NULL && e->index != mr->receiver_index; e = e->next)
				;
			if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) {
				for (nd = peers; nd; nd = nd->next)
					if (&nd->p->handshake.entry == e)
						target = nd;
				if (target != NULL && target->snap.state == HANDSHAKE_CREATED_INITIATION) {
					struct m_state before;
					bytes_copy(before.ck, target->snap.chaining_key, 32);
					bytes_copy(before.h, target->snap.hash, 32);
					acc_resp = m_consume_response(&st, &before, target->snap.ephemeral_private, id.priv,
								      target->snap.preshared_key, mr->unencrypted_ephemeral,
								      mr->encrypted_nothing);
				}
			}
		} else if (fwd && kind == 3) {
			for (e = itd.head; e != NULL && e->index != mc->receiver_index; e = e->next)
				;
			if (e != NULL && (e->type & (INDEX_HASHTABLE_HANDSHAKE | INDEX_HASHTABLE_KEYPAIR)))
				for (nd = peers; nd; nd = nd->next)
					if (nd->p == e->peer && target == NULL)
						target = nd;
			if (target != NULL &&
			    (!target->rest.cookie.have_sent_mac1 ||
			     !xchacha20poly1305_decrypt(pt, mc->encrypted_cookie, 32, target->rest.cookie.last_mac1_sent, 16,
							mc->nonce, target->rest.cookie.cookie_decryption_key)))
				target = NULL;
		}

		dev_take(&ds, &wd);
		head0 = itd.head;
		skb_take(&sks, &skb);
		shim_take(&ss);
		rx_reset();
		secret_birth = wd.cookie_checker.secret_birthdate;
		bytes_copy(secret, wd.cookie_checker.secret, 32);
		dispatch(&wd, &skb);

		// the model: the load, the macs (with the secret's rotation), the path
		path = 0;   // 0: nothing, 1: consume, 2: cookie reply sent
		rotated = 0;
		if (fwd && (kind == 1 || kind == 2)) {
			ul = wg_shim_handshake_queue_len >= 512;
			if (ul) {
				m_lul = now;
			} else if (m_lul != 0) {
				ul = !m_expired(m_lul, 1, now);
				if (!ul)
					m_lul = 0;
			}
			m_mac(mac, mk1, 32, img, len - 32);
			if (!bytes_eq(mac, img + len - 32, 16)) {
				verdict = INVALID_MAC;
			} else if (!ul) {
				verdict = VALID_MAC_BUT_NO_COOKIE;
			} else {
				if (m_expired(secret_birth, 120, now)) {
					// rotated: the new secret is the shim's fresh draw (which one is checked below: the last draw,
					// or the one before if a cookie reply drew its nonce after it); the model takes it from
					// the device and the check below ties it to the draw
					rotated = 1;
					secret_birth = now;
					bytes_copy(secret, wd.cookie_checker.secret, 32);
				}
				m_cookie(c, secret, &skb);
				m_mac(mac, c, 16, img, len - 16);
				if (!bytes_eq(mac, img + len - 16, 16))
					verdict = VALID_MAC_BUT_NO_COOKIE;
				else if (!wg_shim_ratelimit_allow)
					verdict = VALID_MAC_WITH_COOKIE_BUT_RATELIMITED;
				else
					verdict = VALID_MAC_WITH_COOKIE;
			}
			if ((ul && verdict == VALID_MAC_WITH_COOKIE) || (!ul && verdict == VALID_MAC_BUT_NO_COOKIE))
				path = 1;
			else if (ul && verdict == VALID_MAC_BUT_NO_COOKIE)
				path = 2;
			if (rotated)
				CHECK(bytes_eq(secret, path == 2 ? wg_shim_random_log_prev : wg_shim_random_log, 32));
		} else if (fwd) {
			path = 1;   // a cookie reply is consumed without macs
		}
		bytes_copy(ds.secret, secret, 32);
		ds.secret_birthdate = secret_birth;

		// the packet and the skb are never modified; the device changes only by the rotation
		CHECK(skb_same(&sks, &skb) && bytes_eq(skb.data, img, len));
		CHECK(dev_same(&ds, &wd));
		if (path == 1 && kind == 1 && acc_init) {
			struct noise_handshake *h = &target->p->handshake;
			const struct hs_snap *s = &target->snap;
			CHECK(rx_authenticated(target->p, &skb, 1, 0));
			CHECK(h->state == HANDSHAKE_CONSUMED_INITIATION &&
			      bytes_eq(h->remote_ephemeral, mi->unencrypted_ephemeral, 32) &&
			      bytes_eq(h->latest_timestamp, ci.ts, 12) && bytes_eq(h->hash, ci.st.h, 32) &&
			      bytes_eq(h->chaining_key, ci.st.ck, 32) && h->remote_index == mi->sender_index &&
			      h->last_initiation_consumption == m_last_consumption(s->last_initiation_consumption, now));
			CHECK(h->entry.peer == s->peer && h->entry.next == s->next && h->entry.hashed == s->hashed &&
			      h->entry.type == s->type && h->entry.index == s->index && h->static_identity == s->static_identity &&
			      bytes_eq(h->ephemeral_private, s->ephemeral_private, 32) &&
			      bytes_eq(h->remote_static, s->remote_static, 32) &&
			      bytes_eq(h->precomputed_static_static, s->precomputed_static_static, 32) &&
			      bytes_eq(h->preshared_key, s->preshared_key, 32));
			CHECK(target->p->refcount.refcount == target->refs && pr_same(&target->rest, target->p));
			CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes) && shim_same(&ss));
		} else if (path == 1 && kind == 2 && acc_resp) {
			// consume_response, then begin_session: zeroed and a keypair, unless the allocation failed; the
			// keypair becomes current with the handshake's index, unless P is dead (then it is freed)
			struct noise_handshake *h = &target->p->handshake;
			const struct hs_snap *s = &target->snap;
			int alloc_ok = wg_shim_alloc_failures == ss.alloc_failures;
			int session = alloc_ok && !target->rest.is_dead;
			size_t hashed = 0;
			CHECK(rx_authenticated(target->p, &skb, 0, (unsigned int)session));
			CHECK(target->p->refcount.refcount == target->refs && shim_no_warning(&ss));
			if (!alloc_ok) {
				CHECK(wg_shim_allocs == ss.allocs && wg_shim_frees == ss.frees &&
				      wg_shim_alloc_failures == ss.alloc_failures + 1);
				CHECK(h->state == HANDSHAKE_CONSUMED_RESPONSE &&
				      bytes_eq(h->remote_ephemeral, mr->unencrypted_ephemeral, 32) &&
				      bytes_eq(h->hash, st.h, 32) && bytes_eq(h->chaining_key, st.ck, 32) &&
				      h->remote_index == mr->sender_index);
				CHECK(h->entry.peer == s->peer && h->entry.next == s->next && h->entry.hashed == s->hashed &&
				      h->entry.type == s->type && h->entry.index == s->index &&
				      h->static_identity == s->static_identity &&
				      bytes_eq(h->ephemeral_private, s->ephemeral_private, 32) &&
				      bytes_eq(h->remote_static, s->remote_static, 32) &&
				      bytes_eq(h->precomputed_static_static, s->precomputed_static_static, 32) &&
				      bytes_eq(h->preshared_key, s->preshared_key, 32) &&
				      bytes_eq(h->latest_timestamp, s->latest_timestamp, 12) &&
				      h->last_initiation_consumption == s->last_initiation_consumption);
			} else {
				CHECK(hs_zeroed_from(s, h) && wg_shim_allocs == ss.allocs + 1 &&
				      wg_shim_alloc_failures == ss.alloc_failures);
				if (session) {
					struct noise_keypair *kp = target->p->keypairs.current_keypair;
					CHECK(!h->entry.hashed && wg_shim_frees == ss.frees);
					CHECK(kp != NULL && kp->i_am_the_initiator && kp->entry.peer == target->p &&
					      kp->entry.index == s->index && table_has(&itd, &kp->entry) &&
					      kp->remote_index == mr->sender_index);
					wg_noise_keypairs_clear(&target->p->keypairs);   // back to a state of the same shape
					CHECK(wg_shim_frees == ss.frees + 1);
				} else {
					CHECK(h->entry.hashed && h->entry.index == s->index && wg_shim_frees == ss.frees + 1);
				}
			}
			CHECK(pr_same(&target->rest, target->p));
			// every other peer as a whole but its entry's list link; the table: the same entries
			for (nd = peers; nd; nd = nd->next) {
				if (nd == target)
					continue;
				CHECK(hs_same_but_next(&nd->snap, &nd->p->handshake) && nd->p->refcount.refcount == nd->refs &&
				      pr_same(&nd->rest, nd->p));
				if (nd->snap.hashed) {
					CHECK(table_has(&itd, &nd->p->handshake.entry));
					hashed++;
				}
			}
			if (h->entry.hashed) {
				CHECK(table_has(&itd, &h->entry));
				hashed++;
			}
			CHECK(kents_same_but_next(kes, &itd) && table_len(&itd) == hashed + kents_hashed(kes));
		} else if (path == 1 && kind == 3 && target != NULL) {
			struct cookie *ck = &target->p->latest_cookie;
			CHECK(rx_only_cookie(0));
			CHECK(bytes_eq(ck->cookie, pt, 16) && ck->birthdate == now && ck->is_valid && !ck->have_sent_mac1 &&
			      bytes_eq(ck->last_mac1_sent, target->rest.cookie.last_mac1_sent, 16) &&
			      bytes_eq(ck->cookie_decryption_key, target->rest.cookie.cookie_decryption_key, 32) &&
			      bytes_eq(ck->message_mac1_key, target->rest.cookie.message_mac1_key, 32));
			CHECK(hs_same(&target->snap, &target->p->handshake) && target->p->refcount.refcount == target->refs &&
			      pr_same_but_cookie(&target->rest, target->p));
			CHECK(hnodes_same_except(peers, target->p) && itd.head == head0 && kents_same(kes) && shim_same(&ss));
		} else {
			// dropped, rejected, or answered with a cookie reply: nothing changes (but the rotation)
			if (path == 2) {
				CHECK(rx_only_cookie(1));
				CHECK(wg_shim_rx.cookie_index == (kind == 1 ? mi->sender_index : mr->sender_index));
			} else {
				CHECK(rx_only_cookie(0));
			}
			CHECK(hnodes_same_except(peers, NULL) && itd.head == head0 && kents_same(kes) && shim_same(&ss));
		}
		free(skb.data);
		free(img);
	}
	kents_free(kes);
	hnodes_free(peers);
	return 0;
}
