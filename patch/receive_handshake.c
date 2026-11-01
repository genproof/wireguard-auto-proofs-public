// SPDX-License-Identifier: GPL-2.0
/*
 * receive_handshake.c: the receive side of the handshake in drivers/net/wireguard/receive.c, extracted for the
 * law handshake_receive.  Copyright (C) 2015-2019 Jason A. Donenfeld <Jason@zx2c4.com>.  All Rights
 * Reserved.
 *
 * QUICKPROOF S22 (DEVIATIONS.md): the two blocks between the BEGIN/END markers are upstream's text byte for byte
 * (receive.c at the pinned commit: the macro SKB_TYPE_LE32 with validate_header_len, and
 * wg_receive_handshake_packet); patch/tests/extract_check.py checks it.  The rest of receive.c (UDP/IP parsing in
 * prepare_skb_header, the handshake queue and its worker, the data path) is not compiled.  This file is NOT a
 * library unit: harness/handshake_receive.c includes it, so it is part of that law's program only and no other
 * law's program changes.
 *
 * QUICKPROOF S23: what the extracted text calls outside the verified units (send.c, socket.c, timers.c, the device's
 * statistics and handshake queue) is the small shim below.  Every call is recorded in wg_shim_rx for the law;
 * wg_packet_send_handshake_cookie is send.c's body without the socket send (it builds the cookie reply with the
 * verified wg_cookie_message_create); the others only record.  The handshake queue's length (an atomic_t of the
 * full struct wg_device, which the shim's device does not have) is wg_shim_handshake_queue_len, set by the harness:
 * atomic_read() reads it (the macro drops its argument, so the extracted text is unchanged).  net_dbg_*, WARN and
 * local_bh_* are no-ops (S01/S02); the debug messages' arguments are not evaluated.
 */
#include "quickproof_kernel.h"
#include "quickproof_net.h"
#include "noise.h"
#include "cookie.h"
#include "peer.h"
#include "device.h"
#include "messages.h"
#include "timers.h"

/* ---- QUICKPROOF S23 the environment of the extracted text ---- */
int wg_shim_handshake_queue_len;
#define atomic_read(v) (wg_shim_handshake_queue_len)
#define net_dbg_skb_ratelimited(...) ((void)0)
#define WARN(c, ...) (!!(c))
#define local_bh_disable() ((void)0)
#define local_bh_enable() ((void)0)

/* the calls the extracted text makes outside the verified units, recorded (the harness zeroes it before a call) */
struct wg_shim_rx_log {
	unsigned int cookie;              /* wg_packet_send_handshake_cookie */
	__le32 cookie_index;              /* its sender_index argument */
	unsigned int endpoint;            /* wg_socket_set_peer_endpoint_from_skb */
	const struct sk_buff *endpoint_skb;
	unsigned int response;            /* wg_packet_send_handshake_response */
	unsigned int session_derived;     /* wg_timers_session_derived */
	unsigned int handshake_complete;  /* wg_timers_handshake_complete */
	unsigned int keepalive;           /* wg_packet_send_keepalive */
	unsigned int rx_stats;            /* update_rx_stats */
	size_t rx_len;                    /* its length argument */
	unsigned int received;            /* wg_timers_any_authenticated_packet_received */
	unsigned int traversal;           /* wg_timers_any_authenticated_packet_traversal */
	struct wg_peer *peer;             /* the peer argument of the first peer call */
	bool other_peer;                  /* a later peer call had another peer */
};
struct wg_shim_rx_log wg_shim_rx;

static void wg_shim_rx_peer(struct wg_peer *peer)
{
	if (wg_shim_rx.peer == NULL)
		wg_shim_rx.peer = peer;
	else if (wg_shim_rx.peer != peer)
		wg_shim_rx.other_peer = true;
}

/* send.c, without wg_socket_send_buffer_as_reply_to_skb */
static void wg_packet_send_handshake_cookie(struct wg_device *wg, struct sk_buff *initiating_skb,
					    __le32 sender_index)
{
	struct message_handshake_cookie packet;

	wg_cookie_message_create(&packet, initiating_skb, sender_index, &wg->cookie_checker);
	wg_shim_rx.cookie++;
	wg_shim_rx.cookie_index = sender_index;
}

static void wg_socket_set_peer_endpoint_from_skb(struct wg_peer *peer, const struct sk_buff *skb)
{
	wg_shim_rx.endpoint++;
	wg_shim_rx.endpoint_skb = skb;
	wg_shim_rx_peer(peer);
}

static void wg_packet_send_handshake_response(struct wg_peer *peer)
{
	wg_shim_rx.response++;
	wg_shim_rx_peer(peer);
}

static void wg_timers_session_derived(struct wg_peer *peer)
{
	wg_shim_rx.session_derived++;
	wg_shim_rx_peer(peer);
}

static void wg_timers_handshake_complete(struct wg_peer *peer)
{
	wg_shim_rx.handshake_complete++;
	wg_shim_rx_peer(peer);
}

static void wg_packet_send_keepalive(struct wg_peer *peer)
{
	wg_shim_rx.keepalive++;
	wg_shim_rx_peer(peer);
}

static void wg_timers_any_authenticated_packet_received(struct wg_peer *peer)
{
	wg_shim_rx.received++;
	wg_shim_rx_peer(peer);
}

static void wg_timers_any_authenticated_packet_traversal(struct wg_peer *peer)
{
	wg_shim_rx.traversal++;
	wg_shim_rx_peer(peer);
}

/* receive.c's own update_rx_stats updates the net device's counters and peer->rx_bytes (not in the shim's peer) */
static void update_rx_stats(struct wg_peer *peer, size_t len)
{
	wg_shim_rx.rx_stats++;
	wg_shim_rx.rx_len = len;
	wg_shim_rx_peer(peer);
}

/* ---- BEGIN UPSTREAM receive.c (1) ---- */
#define SKB_TYPE_LE32(skb) (((struct message_header *)(skb)->data)->type)

static size_t validate_header_len(struct sk_buff *skb)
{
	if (unlikely(skb->len < sizeof(struct message_header)))
		return 0;
	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_DATA) &&
	    skb->len >= MESSAGE_MINIMUM_LENGTH)
		return sizeof(struct message_data);
	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_INITIATION) &&
	    skb->len == sizeof(struct message_handshake_initiation))
		return sizeof(struct message_handshake_initiation);
	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_RESPONSE) &&
	    skb->len == sizeof(struct message_handshake_response))
		return sizeof(struct message_handshake_response);
	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_COOKIE) &&
	    skb->len == sizeof(struct message_handshake_cookie))
		return sizeof(struct message_handshake_cookie);
	return 0;
}

/* ---- END UPSTREAM receive.c (1) ---- */

/* ---- BEGIN UPSTREAM receive.c (2) ---- */
static void wg_receive_handshake_packet(struct wg_device *wg,
					struct sk_buff *skb)
{
	enum cookie_mac_state mac_state;
	struct wg_peer *peer = NULL;
	/* This is global, so that our load calculation applies to the whole
	 * system. We don't care about races with it at all.
	 */
	static u64 last_under_load;
	bool packet_needs_cookie;
	bool under_load;

	if (SKB_TYPE_LE32(skb) == cpu_to_le32(MESSAGE_HANDSHAKE_COOKIE)) {
		net_dbg_skb_ratelimited("%s: Receiving cookie response from %pISpfsc\n",
					wg->dev->name, skb);
		wg_cookie_message_consume(
			(struct message_handshake_cookie *)skb->data, wg);
		return;
	}

	under_load = atomic_read(&wg->handshake_queue_len) >=
			MAX_QUEUED_INCOMING_HANDSHAKES / 8;
	if (under_load) {
		last_under_load = ktime_get_coarse_boottime_ns();
	} else if (last_under_load) {
		under_load = !wg_birthdate_has_expired(last_under_load, 1);
		if (!under_load)
			last_under_load = 0;
	}
	mac_state = wg_cookie_validate_packet(&wg->cookie_checker, skb,
					      under_load);
	if ((under_load && mac_state == VALID_MAC_WITH_COOKIE) ||
	    (!under_load && mac_state == VALID_MAC_BUT_NO_COOKIE)) {
		packet_needs_cookie = false;
	} else if (under_load && mac_state == VALID_MAC_BUT_NO_COOKIE) {
		packet_needs_cookie = true;
	} else {
		net_dbg_skb_ratelimited("%s: Invalid MAC of handshake, dropping packet from %pISpfsc\n",
					wg->dev->name, skb);
		return;
	}

	switch (SKB_TYPE_LE32(skb)) {
	case cpu_to_le32(MESSAGE_HANDSHAKE_INITIATION): {
		struct message_handshake_initiation *message =
			(struct message_handshake_initiation *)skb->data;

		if (packet_needs_cookie) {
			wg_packet_send_handshake_cookie(wg, skb,
							message->sender_index);
			return;
		}
		peer = wg_noise_handshake_consume_initiation(message, wg);
		if (unlikely(!peer)) {
			net_dbg_skb_ratelimited("%s: Invalid handshake initiation from %pISpfsc\n",
						wg->dev->name, skb);
			return;
		}
		wg_socket_set_peer_endpoint_from_skb(peer, skb);
		net_dbg_ratelimited("%s: Receiving handshake initiation from peer %llu (%pISpfsc)\n",
				    wg->dev->name, peer->internal_id,
				    &peer->endpoint.addr);
		wg_packet_send_handshake_response(peer);
		break;
	}
	case cpu_to_le32(MESSAGE_HANDSHAKE_RESPONSE): {
		struct message_handshake_response *message =
			(struct message_handshake_response *)skb->data;

		if (packet_needs_cookie) {
			wg_packet_send_handshake_cookie(wg, skb,
							message->sender_index);
			return;
		}
		peer = wg_noise_handshake_consume_response(message, wg);
		if (unlikely(!peer)) {
			net_dbg_skb_ratelimited("%s: Invalid handshake response from %pISpfsc\n",
						wg->dev->name, skb);
			return;
		}
		wg_socket_set_peer_endpoint_from_skb(peer, skb);
		net_dbg_ratelimited("%s: Receiving handshake response from peer %llu (%pISpfsc)\n",
				    wg->dev->name, peer->internal_id,
				    &peer->endpoint.addr);
		if (wg_noise_handshake_begin_session(&peer->handshake,
						     &peer->keypairs)) {
			wg_timers_session_derived(peer);
			wg_timers_handshake_complete(peer);
			/* Calling this function will either send any existing
			 * packets in the queue and not send a keepalive, which
			 * is the best case, Or, if there's nothing in the
			 * queue, it will send a keepalive, in order to give
			 * immediate confirmation of the session.
			 */
			wg_packet_send_keepalive(peer);
		}
		break;
	}
	}

	if (unlikely(!peer)) {
		WARN(1, "Somehow a wrong type of packet wound up in the handshake queue!\n");
		return;
	}

	local_bh_disable();
	update_rx_stats(peer, skb->len);
	local_bh_enable();

	wg_timers_any_authenticated_packet_received(peer);
	wg_timers_any_authenticated_packet_traversal(peer);
	wg_peer_put(peer);
}

/* ---- END UPSTREAM receive.c (2) ---- */
