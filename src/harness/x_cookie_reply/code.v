From Coq Require Import String List ZArith.
From compcert Require Import Coqlib Integers Floats AST Ctypes Cop Clight Clightdefs.
Import Clightdefs.ClightNotations.
Local Open Scope Z_scope.
Local Open Scope string_scope.
Local Open Scope clight_scope.

Module Info.
  Definition version := "3.15".
  Definition build_number := "".
  Definition build_tag := "".
  Definition build_branch := "".
  Definition arch := "x86".
  Definition model := "64".
  Definition abi := "standard".
  Definition bitsize := 64.
  Definition big_endian := false.
  Definition source_file := "harness/x_cookie_reply.c".
  Definition normalized := true.
End Info.

Definition _x_cookie_reply__M_BASEPOINT : ident := $"x_cookie_reply__M_BASEPOINT".
Definition _x_cookie_reply__M_LABEL_COOKIE : ident := $"x_cookie_reply__M_LABEL_COOKIE".
Definition ___blake2s_init : ident := $"__blake2s_init".
Definition ___builtin_ais_annot : ident := $"__builtin_ais_annot".
Definition ___builtin_annot : ident := $"__builtin_annot".
Definition ___builtin_annot_intval : ident := $"__builtin_annot_intval".
Definition ___builtin_bswap : ident := $"__builtin_bswap".
Definition ___builtin_bswap16 : ident := $"__builtin_bswap16".
Definition ___builtin_bswap32 : ident := $"__builtin_bswap32".
Definition ___builtin_bswap64 : ident := $"__builtin_bswap64".
Definition ___builtin_clz : ident := $"__builtin_clz".
Definition ___builtin_clzl : ident := $"__builtin_clzl".
Definition ___builtin_clzll : ident := $"__builtin_clzll".
Definition ___builtin_ctz : ident := $"__builtin_ctz".
Definition ___builtin_ctzl : ident := $"__builtin_ctzl".
Definition ___builtin_ctzll : ident := $"__builtin_ctzll".
Definition ___builtin_debug : ident := $"__builtin_debug".
Definition ___builtin_expect : ident := $"__builtin_expect".
Definition ___builtin_fabs : ident := $"__builtin_fabs".
Definition ___builtin_fabsf : ident := $"__builtin_fabsf".
Definition ___builtin_fmadd : ident := $"__builtin_fmadd".
Definition ___builtin_fmax : ident := $"__builtin_fmax".
Definition ___builtin_fmin : ident := $"__builtin_fmin".
Definition ___builtin_fmsub : ident := $"__builtin_fmsub".
Definition ___builtin_fnmadd : ident := $"__builtin_fnmadd".
Definition ___builtin_fnmsub : ident := $"__builtin_fnmsub".
Definition ___builtin_fsqrt : ident := $"__builtin_fsqrt".
Definition ___builtin_membar : ident := $"__builtin_membar".
Definition ___builtin_memcpy_aligned : ident := $"__builtin_memcpy_aligned".
Definition ___builtin_read16_reversed : ident := $"__builtin_read16_reversed".
Definition ___builtin_read32_reversed : ident := $"__builtin_read32_reversed".
Definition ___builtin_sel : ident := $"__builtin_sel".
Definition ___builtin_sqrt : ident := $"__builtin_sqrt".
Definition ___builtin_unreachable : ident := $"__builtin_unreachable".
Definition ___builtin_va_arg : ident := $"__builtin_va_arg".
Definition ___builtin_va_copy : ident := $"__builtin_va_copy".
Definition ___builtin_va_end : ident := $"__builtin_va_end".
Definition ___builtin_va_start : ident := $"__builtin_va_start".
Definition ___builtin_write16_reversed : ident := $"__builtin_write16_reversed".
Definition ___builtin_write32_reversed : ident := $"__builtin_write32_reversed".
Definition ___compcert_i64_dtos : ident := $"__compcert_i64_dtos".
Definition ___compcert_i64_dtou : ident := $"__compcert_i64_dtou".
Definition ___compcert_i64_sar : ident := $"__compcert_i64_sar".
Definition ___compcert_i64_sdiv : ident := $"__compcert_i64_sdiv".
Definition ___compcert_i64_shl : ident := $"__compcert_i64_shl".
Definition ___compcert_i64_shr : ident := $"__compcert_i64_shr".
Definition ___compcert_i64_smod : ident := $"__compcert_i64_smod".
Definition ___compcert_i64_smulh : ident := $"__compcert_i64_smulh".
Definition ___compcert_i64_stod : ident := $"__compcert_i64_stod".
Definition ___compcert_i64_stof : ident := $"__compcert_i64_stof".
Definition ___compcert_i64_udiv : ident := $"__compcert_i64_udiv".
Definition ___compcert_i64_umod : ident := $"__compcert_i64_umod".
Definition ___compcert_i64_umulh : ident := $"__compcert_i64_umulh".
Definition ___compcert_i64_utod : ident := $"__compcert_i64_utod".
Definition ___compcert_i64_utof : ident := $"__compcert_i64_utof".
Definition ___compcert_va_composite : ident := $"__compcert_va_composite".
Definition ___compcert_va_float64 : ident := $"__compcert_va_float64".
Definition ___compcert_va_int32 : ident := $"__compcert_va_int32".
Definition ___compcert_va_int64 : ident := $"__compcert_va_int64".
Definition ___gp_atomic64_t : ident := $"__gp_atomic64_t".
Definition ___gp_spinlock_t : ident := $"__gp_spinlock_t".
Definition _a : ident := $"a".
Definition _alen : ident := $"alen".
Definition _alloc_failures : ident := $"alloc_failures".
Definition _allocs : ident := $"allocs".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _blake2s : ident := $"blake2s".
Definition _blake2s_ctx : ident := $"blake2s_ctx".
Definition _blake2s_final : ident := $"blake2s_final".
Definition _blake2s_init : ident := $"blake2s_init".
Definition _blake2s_update : ident := $"blake2s_update".
Definition _blen : ident := $"blen".
Definition _bt0 : ident := $"bt0".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_set : ident := $"bytes_set".
Definition _bytes_zero : ident := $"bytes_zero".
Definition _c : ident := $"c".
Definition _chaining_key : ident := $"chaining_key".
Definition _check_failed : ident := $"check_failed".
Definition _checker_device : ident := $"checker_device".
Definition _ck_same : ident := $"ck_same".
Definition _ck_snap : ident := $"ck_snap".
Definition _ck_take : ident := $"ck_take".
Definition _cn : ident := $"cn".
Definition _cnode : ident := $"cnode".
Definition _cns : ident := $"cns".
Definition _cookie : ident := $"cookie".
Definition _cookie__1 : ident := $"cookie__1".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _cookie_img : ident := $"cookie_img".
Definition _copy : ident := $"copy".
Definition _counter : ident := $"counter".
Definition _cs : ident := $"cs".
Definition _ctx : ident := $"ctx".
Definition _current_keypair : ident := $"current_keypair".
Definition _curve25519_generic : ident := $"curve25519_generic".
Definition _d : ident := $"d".
Definition _da : ident := $"da".
Definition _data : ident := $"data".
Definition _db : ident := $"db".
Definition _dev : ident := $"dev".
Definition _dev_same : ident := $"dev_same".
Definition _dev_snap : ident := $"dev_snap".
Definition _dev_take : ident := $"dev_take".
Definition _device : ident := $"device".
Definition _draw_boottime : ident := $"draw_boottime".
Definition _draw_peer_refs : ident := $"draw_peer_refs".
Definition _draw_size : ident := $"draw_size".
Definition _draw_steps : ident := $"draw_steps".
Definition _draw_u64 : ident := $"draw_u64".
Definition _e : ident := $"e".
Definition _edge : ident := $"edge".
Definition _enc : ident := $"enc".
Definition _encrypted_cookie : ident := $"encrypted_cookie".
Definition _entry : ident := $"entry".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _except : ident := $"except".
Definition _f : ident := $"f".
Definition _fill : ident := $"fill".
Definition _fill_cookie_msg : ident := $"fill_cookie_msg".
Definition _frees : ident := $"frees".
Definition _h : ident := $"h".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _hashed0 : ident := $"hashed0".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _head0 : ident := $"head0".
Definition _header : ident := $"header".
Definition _hi : ident := $"hi".
Definition _hnode : ident := $"hnode".
Definition _hnodes_add : ident := $"hnodes_add".
Definition _hnodes_free : ident := $"hnodes_free".
Definition _hnodes_pick : ident := $"hnodes_pick".
Definition _hnodes_same_except : ident := $"hnodes_same_except".
Definition _hnodes_snap : ident := $"hnodes_snap".
Definition _honest : ident := $"honest".
Definition _hs_same : ident := $"hs_same".
Definition _hs_snap : ident := $"hs_snap".
Definition _hs_take : ident := $"hs_take".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _ib : ident := $"ib".
Definition _id : ident := $"id".
Definition _id0 : ident := $"id0".
Definition _img : ident := $"img".
Definition _img2 : ident := $"img2".
Definition _in : ident := $"in".
Definition _in6_addr : ident := $"in6_addr".
Definition _in_addr : ident := $"in_addr".
Definition _index : ident := $"index".
Definition _index0 : ident := $"index0".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _initiator0 : ident := $"initiator0".
Definition _inlen : ident := $"inlen".
Definition _internal_id : ident := $"internal_id".
Definition _ip4 : ident := $"ip4".
Definition _ip6 : ident := $"ip6".
Definition _iphdr : ident := $"iphdr".
Definition _ipv6hdr : ident := $"ipv6hdr".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _it : ident := $"it".
Definition _ita : ident := $"ita".
Definition _itab : ident := $"itab".
Definition _itb : ident := $"itb".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _kent : ident := $"kent".
Definition _kent_same_but_next : ident := $"kent_same_but_next".
Definition _kents_add : ident := $"kents_add".
Definition _kents_free : ident := $"kents_free".
Definition _kents_same : ident := $"kents_same".
Definition _kents_snap : ident := $"kents_snap".
Definition _kes : ident := $"kes".
Definition _key : ident := $"key".
Definition _keylen : ident := $"keylen".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kk : ident := $"kk".
Definition _kk__1 : ident := $"kk__1".
Definition _kp : ident := $"kp".
Definition _kref : ident := $"kref".
Definition _l : ident := $"l".
Definition _label : ident := $"label".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _le32_store : ident := $"le32_store".
Definition _len : ident := $"len".
Definition _lock : ident := $"lock".
Definition _m : ident := $"m".
Definition _m_clamp : ident := $"m_clamp".
Definition _m_cookie : ident := $"m_cookie".
Definition _m_dh : ident := $"m_dh".
Definition _m_expired : ident := $"m_expired".
Definition _m_hash2 : ident := $"m_hash2".
Definition _m_identity : ident := $"m_identity".
Definition _m_identity_of : ident := $"m_identity_of".
Definition _m_label_key : ident := $"m_label_key".
Definition _m_mac : ident := $"m_mac".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _message_handshake_cookie : ident := $"message_handshake_cookie".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _mode : ident := $"mode".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _net_device : ident := $"net_device".
Definition _next : ident := $"next".
Definition _next0 : ident := $"next0".
Definition _next_keypair : ident := $"next_keypair".
Definition _noise_handshake : ident := $"noise_handshake".
Definition _noise_keypair : ident := $"noise_keypair".
Definition _noise_keypairs : ident := $"noise_keypairs".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _noise_static_identity : ident := $"noise_static_identity".
Definition _noise_symmetric_key : ident := $"noise_symmetric_key".
Definition _nonce : ident := $"nonce".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _now : ident := $"now".
Definition _np : ident := $"np".
Definition _ok : ident := $"ok".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _owner : ident := $"owner".
Definition _p : ident := $"p".
Definition _peer : ident := $"peer".
Definition _peer0 : ident := $"peer0".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _peer_randomize_rest : ident := $"peer_randomize_rest".
Definition _peer_released : ident := $"peer_released".
Definition _peers : ident := $"peers".
Definition _peers_head : ident := $"peers_head".
Definition _pr_same : ident := $"pr_same".
Definition _pr_same_but_cookie : ident := $"pr_same_but_cookie".
Definition _pr_snap : ident := $"pr_snap".
Definition _pr_take : ident := $"pr_take".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _priv : ident := $"priv".
Definition _protocol : ident := $"protocol".
Definition _psk : ident := $"psk".
Definition _pt : ident := $"pt".
Definition _pta : ident := $"pta".
Definition _ptab : ident := $"ptab".
Definition _ptb : ident := $"ptb".
Definition _pub : ident := $"pub".
Definition _pub_ok : ident := $"pub_ok".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _quickproof_swab16 : ident := $"quickproof_swab16".
Definition _raw : ident := $"raw".
Definition _raw_a : ident := $"raw_a".
Definition _raw_b : ident := $"raw_b".
Definition _raw_priv : ident := $"raw_priv".
Definition _rbirth0 : ident := $"rbirth0".
Definition _rcnt0 : ident := $"rcnt0".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiver_index : ident := $"receiver_index".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _refcount_warn : ident := $"refcount_warn".
Definition _refs : ident := $"refs".
Definition _refs0 : ident := $"refs0".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_index0 : ident := $"remote_index0".
Definition _remote_static : ident := $"remote_static".
Definition _reply : ident := $"reply".
Definition _rest : ident := $"rest".
Definition _rkey0 : ident := $"rkey0".
Definition _rvalid0 : ident := $"rvalid0".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s : ident := $"s".
Definition _s6_addr : ident := $"s6_addr".
Definition _s_addr : ident := $"s_addr".
Definition _saddr : ident := $"saddr".
Definition _saddr4 : ident := $"saddr4".
Definition _saddr6 : ident := $"saddr6".
Definition _sbirth0 : ident := $"sbirth0".
Definition _scnt0 : ident := $"scnt0".
Definition _seconds : ident := $"seconds".
Definition _secret : ident := $"secret".
Definition _secret_birth : ident := $"secret_birth".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _setup_device : ident := $"setup_device".
Definition _setup_peer : ident := $"setup_peer".
Definition _shim_no_warning : ident := $"shim_no_warning".
Definition _shim_same : ident := $"shim_same".
Definition _shim_snap : ident := $"shim_snap".
Definition _shim_take : ident := $"shim_take".
Definition _sk_buff : ident := $"sk_buff".
Definition _skb : ident := $"skb".
Definition _skb_same : ident := $"skb_same".
Definition _skb_snap : ident := $"skb_snap".
Definition _skb_take : ident := $"skb_take".
Definition _skey0 : ident := $"skey0".
Definition _sks : ident := $"sks".
Definition _snap : ident := $"snap".
Definition _source : ident := $"source".
Definition _sport : ident := $"sport".
Definition _ss : ident := $"ss".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _svalid0 : ident := $"svalid0".
Definition _t : ident := $"t".
Definition _target : ident := $"target".
Definition _tn : ident := $"tn".
Definition _type : ident := $"type".
Definition _type0 : ident := $"type0".
Definition _udp : ident := $"udp".
Definition _udphdr : ident := $"udphdr".
Definition _unused : ident := $"unused".
Definition _v : ident := $"v".
Definition _wa : ident := $"wa".
Definition _wb : ident := $"wb".
Definition _wg : ident := $"wg".
Definition _wg_cookie_checker_init : ident := $"wg_cookie_checker_init".
Definition _wg_cookie_checker_precompute_device_keys : ident := $"wg_cookie_checker_precompute_device_keys".
Definition _wg_cookie_checker_precompute_peer_keys : ident := $"wg_cookie_checker_precompute_peer_keys".
Definition _wg_cookie_init : ident := $"wg_cookie_init".
Definition _wg_cookie_message_consume : ident := $"wg_cookie_message_consume".
Definition _wg_cookie_message_create : ident := $"wg_cookie_message_create".
Definition _wg_device : ident := $"wg_device".
Definition _wg_index_hashtable_insert : ident := $"wg_index_hashtable_insert".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_init : ident := $"wg_noise_init".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_shim_alloc_failures : ident := $"wg_shim_alloc_failures".
Definition _wg_shim_allocs : ident := $"wg_shim_allocs".
Definition _wg_shim_boottime_ns : ident := $"wg_shim_boottime_ns".
Definition _wg_shim_frees : ident := $"wg_shim_frees".
Definition _wg_shim_peer_released : ident := $"wg_shim_peer_released".
Definition _wg_shim_random_log : ident := $"wg_shim_random_log".
Definition _wg_shim_random_log_prev : ident := $"wg_shim_random_log_prev".
Definition _wg_shim_refcount_warn : ident := $"wg_shim_refcount_warn".
Definition _x : ident := $"x".
Definition _xchacha20poly1305_decrypt : ident := $"xchacha20poly1305_decrypt".
Definition _xchacha20poly1305_encrypt : ident := $"xchacha20poly1305_encrypt".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'100 : ident := 227%positive.
Definition _t'101 : ident := 228%positive.
Definition _t'102 : ident := 229%positive.
Definition _t'103 : ident := 230%positive.
Definition _t'104 : ident := 231%positive.
Definition _t'105 : ident := 232%positive.
Definition _t'106 : ident := 233%positive.
Definition _t'107 : ident := 234%positive.
Definition _t'108 : ident := 235%positive.
Definition _t'109 : ident := 236%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'110 : ident := 237%positive.
Definition _t'111 : ident := 238%positive.
Definition _t'112 : ident := 239%positive.
Definition _t'113 : ident := 240%positive.
Definition _t'114 : ident := 241%positive.
Definition _t'115 : ident := 242%positive.
Definition _t'116 : ident := 243%positive.
Definition _t'117 : ident := 244%positive.
Definition _t'118 : ident := 245%positive.
Definition _t'119 : ident := 246%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'120 : ident := 247%positive.
Definition _t'121 : ident := 248%positive.
Definition _t'122 : ident := 249%positive.
Definition _t'123 : ident := 250%positive.
Definition _t'124 : ident := 251%positive.
Definition _t'125 : ident := 252%positive.
Definition _t'126 : ident := 253%positive.
Definition _t'127 : ident := 254%positive.
Definition _t'128 : ident := 255%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'32 : ident := 159%positive.
Definition _t'33 : ident := 160%positive.
Definition _t'34 : ident := 161%positive.
Definition _t'35 : ident := 162%positive.
Definition _t'36 : ident := 163%positive.
Definition _t'37 : ident := 164%positive.
Definition _t'38 : ident := 165%positive.
Definition _t'39 : ident := 166%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'40 : ident := 167%positive.
Definition _t'41 : ident := 168%positive.
Definition _t'42 : ident := 169%positive.
Definition _t'43 : ident := 170%positive.
Definition _t'44 : ident := 171%positive.
Definition _t'45 : ident := 172%positive.
Definition _t'46 : ident := 173%positive.
Definition _t'47 : ident := 174%positive.
Definition _t'48 : ident := 175%positive.
Definition _t'49 : ident := 176%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'50 : ident := 177%positive.
Definition _t'51 : ident := 178%positive.
Definition _t'52 : ident := 179%positive.
Definition _t'53 : ident := 180%positive.
Definition _t'54 : ident := 181%positive.
Definition _t'55 : ident := 182%positive.
Definition _t'56 : ident := 183%positive.
Definition _t'57 : ident := 184%positive.
Definition _t'58 : ident := 185%positive.
Definition _t'59 : ident := 186%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'60 : ident := 187%positive.
Definition _t'61 : ident := 188%positive.
Definition _t'62 : ident := 189%positive.
Definition _t'63 : ident := 190%positive.
Definition _t'64 : ident := 191%positive.
Definition _t'65 : ident := 192%positive.
Definition _t'66 : ident := 193%positive.
Definition _t'67 : ident := 194%positive.
Definition _t'68 : ident := 195%positive.
Definition _t'69 : ident := 196%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'70 : ident := 197%positive.
Definition _t'71 : ident := 198%positive.
Definition _t'72 : ident := 199%positive.
Definition _t'73 : ident := 200%positive.
Definition _t'74 : ident := 201%positive.
Definition _t'75 : ident := 202%positive.
Definition _t'76 : ident := 203%positive.
Definition _t'77 : ident := 204%positive.
Definition _t'78 : ident := 205%positive.
Definition _t'79 : ident := 206%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'80 : ident := 207%positive.
Definition _t'81 : ident := 208%positive.
Definition _t'82 : ident := 209%positive.
Definition _t'83 : ident := 210%positive.
Definition _t'84 : ident := 211%positive.
Definition _t'85 : ident := 212%positive.
Definition _t'86 : ident := 213%positive.
Definition _t'87 : ident := 214%positive.
Definition _t'88 : ident := 215%positive.
Definition _t'89 : ident := 216%positive.
Definition _t'9 : ident := 136%positive.
Definition _t'90 : ident := 217%positive.
Definition _t'91 : ident := 218%positive.
Definition _t'92 : ident := 219%positive.
Definition _t'93 : ident := 220%positive.
Definition _t'94 : ident := 221%positive.
Definition _t'95 : ident := 222%positive.
Definition _t'96 : ident := 223%positive.
Definition _t'97 : ident := 224%positive.
Definition _t'98 : ident := 225%positive.
Definition _t'99 : ident := 226%positive.

Definition f_quickproof_swab16 := {|
  fn_return := tushort;
  fn_callconv := cc_default;
  fn_params := ((_x, tushort) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ecast
                 (Ebinop Oor
                   (Ebinop Oshr (Etempvar _x tushort)
                     (Econst_int (Int.repr 8) tint) tint)
                   (Ebinop Oshl (Etempvar _x tushort)
                     (Econst_int (Int.repr 8) tint) tint) tint) tushort)))
|}.

Definition f___blake2s_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: (_key, (tptr tvoid)) ::
                (_keylen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd
        (Efield
          (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
            (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
        (Econst_int (Int.repr 0) tint) (tptr tuint)) tuint)
    (Ebinop Oxor (Econst_int (Int.repr 1779033703) tint)
      (Ebinop Oor
        (Ebinop Oor (Econst_int (Int.repr 16842752) tint)
          (Ebinop Oshl (Etempvar _keylen tulong)
            (Econst_int (Int.repr 8) tint) tulong) tulong)
        (Etempvar _outlen tulong) tulong) tulong))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd
          (Efield
            (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
              (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
          (Econst_int (Int.repr 1) tint) (tptr tuint)) tuint)
      (Econst_int (Int.repr (-1150833019)) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd
            (Efield
              (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
            (Econst_int (Int.repr 2) tint) (tptr tuint)) tuint)
        (Econst_int (Int.repr 1013904242) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd
              (Efield
                (Ederef (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                  (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
              (Econst_int (Int.repr 3) tint) (tptr tuint)) tuint)
          (Econst_int (Int.repr (-1521486534)) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef
                    (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                    (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                (Econst_int (Int.repr 4) tint) (tptr tuint)) tuint)
            (Econst_int (Int.repr 1359893119) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd
                  (Efield
                    (Ederef
                      (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                      (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                  (Econst_int (Int.repr 5) tint) (tptr tuint)) tuint)
              (Econst_int (Int.repr (-1694144372)) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Ederef
                        (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                        (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                    (Econst_int (Int.repr 6) tint) (tptr tuint)) tuint)
                (Econst_int (Int.repr 528734635) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                          (Tstruct _blake2s_ctx noattr)) _h (tarray tuint 8))
                      (Econst_int (Int.repr 7) tint) (tptr tuint)) tuint)
                  (Econst_int (Int.repr 1541459225) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd
                        (Efield
                          (Ederef
                            (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                            (Tstruct _blake2s_ctx noattr)) _t
                          (tarray tuint 2)) (Econst_int (Int.repr 0) tint)
                        (tptr tuint)) tuint) (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd
                          (Efield
                            (Ederef
                              (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                              (Tstruct _blake2s_ctx noattr)) _t
                            (tarray tuint 2)) (Econst_int (Int.repr 1) tint)
                          (tptr tuint)) tuint)
                      (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                (Tstruct _blake2s_ctx noattr)) _f
                              (tarray tuint 2))
                            (Econst_int (Int.repr 0) tint) (tptr tuint))
                          tuint) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                  (Tstruct _blake2s_ctx noattr)) _f
                                (tarray tuint 2))
                              (Econst_int (Int.repr 1) tint) (tptr tuint))
                            tuint) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                (Tstruct _blake2s_ctx noattr)) _buflen tuint)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                  (Tstruct _blake2s_ctx noattr)) _outlen
                                tuint) (Etempvar _outlen tulong))
                            (Sifthenelse (Etempvar _keylen tulong)
                              (Ssequence
                                (Scall None
                                  (Evar _memcpy (Tfunction
                                                  ((tptr tvoid) ::
                                                   (tptr tvoid) :: tulong ::
                                                   nil) (tptr tvoid)
                                                  cc_default))
                                  ((Efield
                                     (Ederef
                                       (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                       (Tstruct _blake2s_ctx noattr)) _buf
                                     (tarray tuchar 64)) ::
                                   (Etempvar _key (tptr tvoid)) ::
                                   (Etempvar _keylen tulong) :: nil))
                                (Ssequence
                                  (Scall None
                                    (Evar _memset (Tfunction
                                                    ((tptr tvoid) :: tint ::
                                                     tulong :: nil)
                                                    (tptr tvoid) cc_default))
                                    ((Ebinop Oadd
                                       (Efield
                                         (Ederef
                                           (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                           (Tstruct _blake2s_ctx noattr))
                                         _buf (tarray tuchar 64))
                                       (Etempvar _keylen tulong)
                                       (tptr tuchar)) ::
                                     (Econst_int (Int.repr 0) tint) ::
                                     (Ebinop Osub
                                       (Econst_int (Int.repr 64) tint)
                                       (Etempvar _keylen tulong) tulong) ::
                                     nil))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr)))
                                        (Tstruct _blake2s_ctx noattr))
                                      _buflen tuint)
                                    (Econst_int (Int.repr 64) tint))))
                              Sskip)))))))))))))))
|}.

Definition f_blake2s_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar ___blake2s_init (Tfunction
                          ((tptr (Tstruct _blake2s_ctx noattr)) :: tulong ::
                           (tptr tvoid) :: tulong :: nil) tvoid cc_default))
  ((Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr))) ::
   (Etempvar _outlen tulong) ::
   (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
   (Econst_int (Int.repr 0) tint) :: nil))
|}.

Definition f_blake2s := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_keylen, tulong) ::
                (_in, (tptr tuchar)) :: (_inlen, tulong) ::
                (_out, (tptr tuchar)) :: (_outlen, tulong) :: nil);
  fn_vars := ((_ctx, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := ((_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall None
      (Evar ___blake2s_init (Tfunction
                              ((tptr (Tstruct _blake2s_ctx noattr)) ::
                               tulong :: (tptr tvoid) :: tulong :: nil) tvoid
                              cc_default))
      ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
         (tptr (Tstruct _blake2s_ctx noattr))) ::
       (Etempvar _outlen tulong) :: (Etempvar _key (tptr tuchar)) ::
       (Etempvar _keylen tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _blake2s_update (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _in (tptr tuchar)) :: (Etempvar _inlen tulong) :: nil))
      (Scall None
        (Evar _blake2s_final (Tfunction
                               ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                (tptr tuchar) :: nil) tvoid cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _out (tptr tuchar)) :: nil)))))
|}.

Definition v_wg_shim_refcount_warn := {|
  gvar_info := (tarray tulong 5);
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_check_failed := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_p, (tptr tint)) :: nil);
  fn_body :=
(Ssequence
  (Sset _p (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Sassign (Ederef (Etempvar _p (tptr tint)) tint)
    (Econst_int (Int.repr 0) tint)))
|}.

Definition f_bytes_eq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_b, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _b (tptr tuchar)) (Etempvar _i tulong)
                  (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_bytes_zero := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                       tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _a (tptr tuchar)) (Etempvar _i tulong)
                (tptr tuchar)) tuchar))
          (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip)))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
          tulong))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_bytes_copy := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_s, (tptr tuchar)) :: (_n, tulong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _s (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
              (tptr tuchar)) tuchar) (Etempvar _t'1 tuchar))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_bytes_set := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr tuchar)) :: (_v, tuchar) :: (_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tulong) (Etempvar _n tulong)
                     tint)
        Sskip
        Sbreak)
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _d (tptr tuchar)) (Etempvar _i tulong)
            (tptr tuchar)) tuchar) (Etempvar _v tuchar)))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_draw_size := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _n (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tulong)
                   (Econst_long (Int64.repr (-1)) tulong) tint)
      (Sset _t'2 (Ecast (Etempvar _n tulong) tulong))
      (Sset _t'2
        (Ecast
          (Ebinop Omod (Etempvar _n tulong)
            (Econst_long (Int64.repr (-1)) tulong) tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_draw_steps := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _n (Etempvar _t'1 tulong)))
  (Ssequence
    (Sifthenelse (Ebinop Ole (Etempvar _n tulong)
                   (Econst_long (Int64.repr (-1)) tulong) tint)
      (Sset _t'2 (Ecast (Etempvar _n tulong) tulong))
      (Sset _t'2
        (Ecast
          (Ebinop Omod (Etempvar _n tulong)
            (Econst_long (Int64.repr (-1)) tulong) tulong) tulong)))
    (Sreturn (Some (Etempvar _t'2 tulong)))))
|}.

Definition f_draw_u64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_hi, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sset _hi (Ecast (Etempvar _t'1 tuint) tulong)))
  (Ssequence
    (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sreturn (Some (Ebinop Oor
                     (Ebinop Oshl (Etempvar _hi tulong)
                       (Econst_int (Int.repr 32) tint) tulong)
                     (Etempvar _t'2 tuint) tulong)))))
|}.

Definition f_draw_boottime := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1) (Evar _draw_u64 (Tfunction nil tulong cc_default)) nil)
  (Sreturn (Some (Ebinop Oand (Etempvar _t'1 tulong)
                   (Ebinop Osub
                     (Ebinop Oshl (Econst_long (Int64.repr 1) tulong)
                       (Econst_int (Int.repr 62) tint) tulong)
                     (Econst_int (Int.repr 1) tint) tulong) tulong))))
|}.

Definition v_wg_shim_boottime_ns := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_random_log := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_random_log_prev := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_allocs := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_alloc_failures := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_frees := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_peer_released := {|
  gvar_info := tulong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_le32_store := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tuchar)) :: (_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Etempvar _p (tptr tuchar)) (Econst_int (Int.repr 0) tint)
        (tptr tuchar)) tuchar) (Ecast (Etempvar _v tuint) tuchar))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _p (tptr tuchar))
          (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
      (Ecast
        (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 8) tint)
          tuint) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 16) tint)
            tuint) tuchar))
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _p (tptr tuchar))
            (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 24) tint)
            tuint) tuchar)))))
|}.

Definition f_m_hash2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_a, (tptr tuchar)) ::
                (_alen, tulong) :: (_b, (tptr tuchar)) :: (_blen, tulong) ::
                nil);
  fn_vars := ((_ctx, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _blake2s_init (Tfunction
                          ((tptr (Tstruct _blake2s_ctx noattr)) :: tulong ::
                           nil) tvoid cc_default))
    ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
       (tptr (Tstruct _blake2s_ctx noattr))) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _blake2s_update (Tfunction
                              ((tptr (Tstruct _blake2s_ctx noattr)) ::
                               (tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
      ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
         (tptr (Tstruct _blake2s_ctx noattr))) ::
       (Etempvar _a (tptr tuchar)) :: (Etempvar _alen tulong) :: nil))
    (Ssequence
      (Scall None
        (Evar _blake2s_update (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _b (tptr tuchar)) :: (Etempvar _blen tulong) :: nil))
      (Scall None
        (Evar _blake2s_final (Tfunction
                               ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                (tptr tuchar) :: nil) tvoid cc_default))
        ((Eaddrof (Evar _ctx (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _out (tptr tuchar)) :: nil)))))
|}.

Definition f_m_dh := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_priv, (tptr tuchar)) ::
                (_pub, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _curve25519_generic (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) ::
                                 (tptr tuchar) :: nil) tvoid cc_default))
    ((Etempvar _out (tptr tuchar)) :: (Etempvar _priv (tptr tuchar)) ::
     (Etempvar _pub (tptr tuchar)) :: nil))
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bytes_zero (Tfunction ((tptr tuchar) :: tulong :: nil) tint
                          cc_default))
      ((Etempvar _out (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Sreturn (Some (Eunop Onotbool (Etempvar _t'1 tint) tint)))))
|}.

Definition v_x_cookie_reply__M_BASEPOINT := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_int8 (Int.repr 9) :: Init_space 31 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_m_clamp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_k, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _k (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _k (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ebinop Oand (Etempvar _t'2 tuchar) (Econst_int (Int.repr 248) tint)
        tint)))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _k (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _k (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
      (Ecast
        (Ebinop Oor
          (Ebinop Oand (Etempvar _t'1 tuchar)
            (Econst_int (Int.repr 127) tint) tint)
          (Econst_int (Int.repr 64) tint) tint) tuchar))))
|}.

Definition f_m_identity_of := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_id, (tptr (Tstruct _m_identity noattr))) ::
                (_raw, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_pub_ok, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _bytes_copy (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
         (Tstruct _m_identity noattr)) _priv (tarray tuchar 32)) ::
     (Etempvar _raw (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _m_clamp (Tfunction ((tptr tuchar) :: nil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
           (Tstruct _m_identity noattr)) _priv (tarray tuchar 32)) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _m_dh (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                         nil) tint cc_default))
          ((Efield
             (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
               (Tstruct _m_identity noattr)) _pub (tarray tuchar 32)) ::
           (Etempvar _raw (tptr tuchar)) ::
           (Evar _x_cookie_reply__M_BASEPOINT (tarray tuchar 32)) :: nil))
        (Sset _pub_ok (Etempvar _t'1 tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'2)
            (Evar _bytes_zero (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tint cc_default))
            ((Etempvar _raw (tptr tuchar)) ::
             (Econst_int (Int.repr 32) tint) :: nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
            (Sset _t'3 (Ecast (Etempvar _pub_ok tint) tbool))
            (Sset _t'3 (Econst_int (Int.repr 0) tint))))
        (Sassign
          (Efield
            (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
              (Tstruct _m_identity noattr)) _ok tint) (Etempvar _t'3 tint))))))
|}.

Definition v_x_cookie_reply__M_LABEL_COOKIE := {|
  gvar_info := (tarray tuchar 8);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_m_label_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_label, (tptr tuchar)) ::
                (_pub, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _m_hash2 (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                    (tptr tuchar) :: tulong :: nil) tvoid cc_default))
  ((Etempvar _out (tptr tuchar)) :: (Etempvar _label (tptr tuchar)) ::
   (Econst_int (Int.repr 8) tint) :: (Etempvar _pub (tptr tuchar)) ::
   (Econst_int (Int.repr 32) tint) :: nil))
|}.

Definition f_m_mac := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_keylen, tulong) :: (_msg, (tptr tuchar)) ::
                (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _blake2s (Tfunction
                   ((tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
                    (tptr tuchar) :: tulong :: nil) tvoid cc_default))
  ((Etempvar _key (tptr tuchar)) :: (Etempvar _keylen tulong) ::
   (Etempvar _msg (tptr tuchar)) :: (Etempvar _len tulong) ::
   (Etempvar _out (tptr tuchar)) :: (Econst_int (Int.repr 16) tint) :: nil))
|}.

Definition f_setup_device := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_wg, (tptr (Tstruct _wg_device noattr))) ::
                (_itab, (tptr (Tstruct _index_hashtable noattr))) ::
                (_ptab, (tptr (Tstruct _pubkey_hashtable noattr))) ::
                (_raw_priv, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
        (Tstruct _wg_device noattr)) _dev
      (tptr (Tstruct _net_device noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _itab (tptr (Tstruct _index_hashtable noattr)))
          (Tstruct _index_hashtable noattr)) _head
        (tptr (Tstruct _index_hashtable_entry noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sassign
        (Efield
          (Ederef (Etempvar _ptab (tptr (Tstruct _pubkey_hashtable noattr)))
            (Tstruct _pubkey_hashtable noattr)) _head
          (tptr (Tstruct _wg_peer noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
              (Tstruct _wg_device noattr)) _index_hashtable
            (tptr (Tstruct _index_hashtable noattr)))
          (Etempvar _itab (tptr (Tstruct _index_hashtable noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                (Tstruct _wg_device noattr)) _peer_hashtable
              (tptr (Tstruct _pubkey_hashtable noattr)))
            (Etempvar _ptab (tptr (Tstruct _pubkey_hashtable noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Efield
                  (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                    (Tstruct _wg_device noattr)) _static_identity
                  (Tstruct _noise_static_identity noattr)) _has_identity
                tbool) (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Scall None
                (Evar _bytes_set (Tfunction
                                   ((tptr tuchar) :: tuchar :: tulong :: nil)
                                   tvoid cc_default))
                ((Efield
                   (Efield
                     (Ederef
                       (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                       (Tstruct _wg_device noattr)) _static_identity
                     (Tstruct _noise_static_identity noattr)) _static_public
                   (tarray tuchar 32)) :: (Econst_int (Int.repr 0) tint) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _bytes_set (Tfunction
                                     ((tptr tuchar) :: tuchar :: tulong ::
                                      nil) tvoid cc_default))
                  ((Efield
                     (Efield
                       (Ederef
                         (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                         (Tstruct _wg_device noattr)) _static_identity
                       (Tstruct _noise_static_identity noattr))
                     _static_private (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 0) tint) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _bytes_set (Tfunction
                                       ((tptr tuchar) :: tuchar :: tulong ::
                                        nil) tvoid cc_default))
                    ((Efield
                       (Efield
                         (Ederef
                           (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                           (Tstruct _wg_device noattr)) _cookie_checker
                         (Tstruct _cookie_checker noattr))
                       _cookie_encryption_key (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bytes_set (Tfunction
                                         ((tptr tuchar) :: tuchar ::
                                          tulong :: nil) tvoid cc_default))
                      ((Efield
                         (Efield
                           (Ederef
                             (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                             (Tstruct _wg_device noattr)) _cookie_checker
                           (Tstruct _cookie_checker noattr))
                         _message_mac1_key (tarray tuchar 32)) ::
                       (Econst_int (Int.repr 0) tint) ::
                       (Econst_int (Int.repr 32) tint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _wg_noise_set_static_identity_private_key 
                        (Tfunction
                          ((tptr (Tstruct _noise_static_identity noattr)) ::
                           (tptr tuchar) :: nil) tvoid cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                               (Tstruct _wg_device noattr)) _static_identity
                             (Tstruct _noise_static_identity noattr))
                           (tptr (Tstruct _noise_static_identity noattr))) ::
                         (Etempvar _raw_priv (tptr tuchar)) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _wg_cookie_checker_init (Tfunction
                                                          ((tptr (Tstruct _cookie_checker noattr)) ::
                                                           (tptr (Tstruct _wg_device noattr)) ::
                                                           nil) tvoid
                                                          cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                 (Tstruct _wg_device noattr)) _cookie_checker
                               (Tstruct _cookie_checker noattr))
                             (tptr (Tstruct _cookie_checker noattr))) ::
                           (Etempvar _wg (tptr (Tstruct _wg_device noattr))) ::
                           nil))
                        (Scall None
                          (Evar _wg_cookie_checker_precompute_device_keys 
                          (Tfunction
                            ((tptr (Tstruct _cookie_checker noattr)) :: nil)
                            tvoid cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                 (Tstruct _wg_device noattr)) _cookie_checker
                               (Tstruct _cookie_checker noattr))
                             (tptr (Tstruct _cookie_checker noattr))) :: nil))))))))))))))
|}.

Definition f_setup_peer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) ::
                (_pub, (tptr tuchar)) :: (_psk, (tptr tuchar)) ::
                (_id, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'2, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'1, (tptr (Tstruct _pubkey_hashtable noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
        (Tstruct _wg_peer noattr)) _device
      (tptr (Tstruct _wg_device noattr)))
    (Etempvar _wg (tptr (Tstruct _wg_device noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
          (Tstruct _wg_peer noattr)) _is_dead tbool)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Efield
          (Efield
            (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
              (Tstruct _wg_peer noattr)) _keypairs
            (Tstruct _noise_keypairs noattr)) _current_keypair
          (tptr (Tstruct _noise_keypair noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _keypairs
              (Tstruct _noise_keypairs noattr)) _previous_keypair
            (tptr (Tstruct _noise_keypair noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _keypairs
                (Tstruct _noise_keypairs noattr)) _next_keypair
              (tptr (Tstruct _noise_keypair noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Sassign
              (Efield
                (Efield
                  (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _last_sent_handshake
                  (Tstruct ___gp_atomic64_t noattr)) _counter tlong)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Efield
                  (Efield
                    (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _refcount
                    (Tstruct _kref noattr)) _refcount tuint)
                (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _internal_id tulong)
                  (Etempvar _id tulong))
                (Ssequence
                  (Sassign
                    (Efield
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _handshake
                          (Tstruct _noise_handshake noattr)) _entry
                        (Tstruct _index_hashtable_entry noattr)) _next
                      (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                  (Ssequence
                    (Sassign
                      (Efield
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _handshake
                            (Tstruct _noise_handshake noattr)) _entry
                          (Tstruct _index_hashtable_entry noattr)) _hashed
                        tbool) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Scall None
                        (Evar _wg_noise_handshake_init (Tfunction
                                                         ((tptr (Tstruct _noise_handshake noattr)) ::
                                                          (tptr (Tstruct _noise_static_identity noattr)) ::
                                                          (tptr tuchar) ::
                                                          (tptr tuchar) ::
                                                          (tptr (Tstruct _wg_peer noattr)) ::
                                                          nil) tvoid
                                                         cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                               (Tstruct _wg_peer noattr)) _handshake
                             (Tstruct _noise_handshake noattr))
                           (tptr (Tstruct _noise_handshake noattr))) ::
                         (Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                               (Tstruct _wg_device noattr)) _static_identity
                             (Tstruct _noise_static_identity noattr))
                           (tptr (Tstruct _noise_static_identity noattr))) ::
                         (Etempvar _pub (tptr tuchar)) ::
                         (Etempvar _psk (tptr tuchar)) ::
                         (Etempvar _peer (tptr (Tstruct _wg_peer noattr))) ::
                         nil))
                      (Ssequence
                        (Scall None
                          (Evar _wg_cookie_init (Tfunction
                                                  ((tptr (Tstruct _cookie noattr)) ::
                                                   nil) tvoid cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                                 (Tstruct _wg_peer noattr)) _latest_cookie
                               (Tstruct _cookie noattr))
                             (tptr (Tstruct _cookie noattr))) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _wg_cookie_checker_precompute_peer_keys 
                            (Tfunction
                              ((tptr (Tstruct _wg_peer noattr)) :: nil) tvoid
                              cc_default))
                            ((Etempvar _peer (tptr (Tstruct _wg_peer noattr))) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'2
                                (Efield
                                  (Ederef
                                    (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                    (Tstruct _wg_device noattr))
                                  _peer_hashtable
                                  (tptr (Tstruct _pubkey_hashtable noattr))))
                              (Ssequence
                                (Sset _t'3
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'2 (tptr (Tstruct _pubkey_hashtable noattr)))
                                      (Tstruct _pubkey_hashtable noattr))
                                    _head (tptr (Tstruct _wg_peer noattr))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _pubkey_next
                                    (tptr (Tstruct _wg_peer noattr)))
                                  (Etempvar _t'3 (tptr (Tstruct _wg_peer noattr))))))
                            (Ssequence
                              (Sset _t'1
                                (Efield
                                  (Ederef
                                    (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                    (Tstruct _wg_device noattr))
                                  _peer_hashtable
                                  (tptr (Tstruct _pubkey_hashtable noattr))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _t'1 (tptr (Tstruct _pubkey_hashtable noattr)))
                                    (Tstruct _pubkey_hashtable noattr)) _head
                                  (tptr (Tstruct _wg_peer noattr)))
                                (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))))))))))))))))))
|}.

Definition f_hs_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _hs_snap noattr))) ::
                (_h, (tptr (Tstruct _noise_handshake noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'9, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'8, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'7, tbool) :: (_t'6, tint) :: (_t'5, tuint) ::
               (_t'4, tint) :: (_t'3, tulong) ::
               (_t'2, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'9
      (Efield
        (Efield
          (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
            (Tstruct _noise_handshake noattr)) _entry
          (Tstruct _index_hashtable_entry noattr)) _peer
        (tptr (Tstruct _wg_peer noattr))))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
          (Tstruct _hs_snap noattr)) _peer (tptr (Tstruct _wg_peer noattr)))
      (Etempvar _t'9 (tptr (Tstruct _wg_peer noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'8
        (Efield
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
              (Tstruct _noise_handshake noattr)) _entry
            (Tstruct _index_hashtable_entry noattr)) _next
          (tptr (Tstruct _index_hashtable_entry noattr))))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
            (Tstruct _hs_snap noattr)) _next
          (tptr (Tstruct _index_hashtable_entry noattr)))
        (Etempvar _t'8 (tptr (Tstruct _index_hashtable_entry noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'7
          (Efield
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _entry
              (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
              (Tstruct _hs_snap noattr)) _hashed tbool)
          (Etempvar _t'7 tbool)))
      (Ssequence
        (Ssequence
          (Sset _t'6
            (Efield
              (Efield
                (Ederef
                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                  (Tstruct _noise_handshake noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _type tint))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                (Tstruct _hs_snap noattr)) _type tint) (Etempvar _t'6 tint)))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                    (Tstruct _noise_handshake noattr)) _entry
                  (Tstruct _index_hashtable_entry noattr)) _index tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                  (Tstruct _hs_snap noattr)) _index tuint)
              (Etempvar _t'5 tuint)))
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                    (Tstruct _noise_handshake noattr)) _state tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                    (Tstruct _hs_snap noattr)) _state tint)
                (Etempvar _t'4 tint)))
            (Ssequence
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr))
                    _last_initiation_consumption tulong))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                      (Tstruct _hs_snap noattr)) _last_initiation_consumption
                    tulong) (Etempvar _t'3 tulong)))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                        (Tstruct _noise_handshake noattr)) _static_identity
                      (tptr (Tstruct _noise_static_identity noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                        (Tstruct _hs_snap noattr)) _static_identity
                      (tptr (Tstruct _noise_static_identity noattr)))
                    (Etempvar _t'2 (tptr (Tstruct _noise_static_identity noattr)))))
                (Ssequence
                  (Scall None
                    (Evar _bytes_copy (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tvoid cc_default))
                    ((Efield
                       (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                         (Tstruct _hs_snap noattr)) _ephemeral_private
                       (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr))
                       _ephemeral_private (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bytes_copy (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tvoid cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                           (Tstruct _hs_snap noattr)) _remote_static
                         (tarray tuchar 32)) ::
                       (Efield
                         (Ederef
                           (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                           (Tstruct _noise_handshake noattr)) _remote_static
                         (tarray tuchar 32)) ::
                       (Econst_int (Int.repr 32) tint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _bytes_copy (Tfunction
                                            ((tptr tuchar) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                             (Tstruct _hs_snap noattr)) _remote_ephemeral
                           (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _remote_ephemeral (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _bytes_copy (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                               (Tstruct _hs_snap noattr))
                             _precomputed_static_static (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _precomputed_static_static (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _bytes_copy (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 nil) tvoid cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                 (Tstruct _hs_snap noattr)) _preshared_key
                               (tarray tuchar 32)) ::
                             (Efield
                               (Ederef
                                 (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _preshared_key (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _bytes_copy (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   nil) tvoid cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                   (Tstruct _hs_snap noattr)) _hash
                                 (tarray tuchar 32)) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr)) _hash
                                 (tarray tuchar 32)) ::
                               (Econst_int (Int.repr 32) tint) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _bytes_copy (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tvoid
                                                    cc_default))
                                ((Efield
                                   (Ederef
                                     (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                     (Tstruct _hs_snap noattr)) _chaining_key
                                   (tarray tuchar 32)) ::
                                 (Efield
                                   (Ederef
                                     (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                     (Tstruct _noise_handshake noattr))
                                   _chaining_key (tarray tuchar 32)) ::
                                 (Econst_int (Int.repr 32) tint) :: nil))
                              (Ssequence
                                (Scall None
                                  (Evar _bytes_copy (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                                  ((Efield
                                     (Ederef
                                       (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                       (Tstruct _hs_snap noattr))
                                     _latest_timestamp (tarray tuchar 12)) ::
                                   (Efield
                                     (Ederef
                                       (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                       (Tstruct _noise_handshake noattr))
                                     _latest_timestamp (tarray tuchar 12)) ::
                                   (Econst_int (Int.repr 12) tint) :: nil))
                                (Ssequence
                                  (Sset _t'1
                                    (Efield
                                      (Ederef
                                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                        (Tstruct _noise_handshake noattr))
                                      _remote_index tuint))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                        (Tstruct _hs_snap noattr))
                                      _remote_index tuint)
                                    (Etempvar _t'1 tuint)))))))))))))))))))
|}.

Definition f_hs_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _hs_snap noattr))) ::
                (_h, (tptr (Tstruct _noise_handshake noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'24, tint) :: (_t'23, tint) :: (_t'22, tint) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'42, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'41, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'40, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'39, (tptr (Tstruct _wg_peer noattr))) :: (_t'38, tbool) ::
               (_t'37, tbool) :: (_t'36, tint) :: (_t'35, tint) ::
               (_t'34, tuint) :: (_t'33, tuint) :: (_t'32, tint) ::
               (_t'31, tint) :: (_t'30, tulong) :: (_t'29, tulong) ::
               (_t'28, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'27, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'26, tuint) :: (_t'25, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'39
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                        (Tstruct _hs_snap noattr)) _peer
                                      (tptr (Tstruct _wg_peer noattr))))
                                  (Ssequence
                                    (Sset _t'40
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _entry
                                          (Tstruct _index_hashtable_entry noattr))
                                        _peer
                                        (tptr (Tstruct _wg_peer noattr))))
                                    (Sifthenelse (Ebinop Oeq
                                                   (Etempvar _t'39 (tptr (Tstruct _wg_peer noattr)))
                                                   (Etempvar _t'40 (tptr (Tstruct _wg_peer noattr)))
                                                   tint)
                                      (Ssequence
                                        (Sset _t'41
                                          (Efield
                                            (Ederef
                                              (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                              (Tstruct _hs_snap noattr))
                                            _next
                                            (tptr (Tstruct _index_hashtable_entry noattr))))
                                        (Ssequence
                                          (Sset _t'42
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                  (Tstruct _noise_handshake noattr))
                                                _entry
                                                (Tstruct _index_hashtable_entry noattr))
                                              _next
                                              (tptr (Tstruct _index_hashtable_entry noattr))))
                                          (Sset _t'1
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _t'41 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                (Etempvar _t'42 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                tint) tbool))))
                                      (Sset _t'1
                                        (Econst_int (Int.repr 0) tint)))))
                                (Sifthenelse (Etempvar _t'1 tint)
                                  (Ssequence
                                    (Sset _t'37
                                      (Efield
                                        (Ederef
                                          (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                          (Tstruct _hs_snap noattr)) _hashed
                                        tbool))
                                    (Ssequence
                                      (Sset _t'38
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                              (Tstruct _noise_handshake noattr))
                                            _entry
                                            (Tstruct _index_hashtable_entry noattr))
                                          _hashed tbool))
                                      (Sset _t'2
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'37 tbool)
                                            (Etempvar _t'38 tbool) tint)
                                          tbool))))
                                  (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'2 tint)
                                (Ssequence
                                  (Sset _t'35
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                        (Tstruct _hs_snap noattr)) _type
                                      tint))
                                  (Ssequence
                                    (Sset _t'36
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _entry
                                          (Tstruct _index_hashtable_entry noattr))
                                        _type tint))
                                    (Sset _t'3
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'35 tint)
                                          (Etempvar _t'36 tint) tint) tbool))))
                                (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'3 tint)
                              (Ssequence
                                (Sset _t'33
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                      (Tstruct _hs_snap noattr)) _index
                                    tuint))
                                (Ssequence
                                  (Sset _t'34
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _entry
                                        (Tstruct _index_hashtable_entry noattr))
                                      _index tuint))
                                  (Sset _t'4
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _t'33 tuint)
                                        (Etempvar _t'34 tuint) tint) tbool))))
                              (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'4 tint)
                            (Ssequence
                              (Sset _t'31
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                    (Tstruct _hs_snap noattr)) _state tint))
                              (Ssequence
                                (Sset _t'32
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                      (Tstruct _noise_handshake noattr))
                                    _state tint))
                                (Sset _t'5
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _t'31 tint)
                                      (Etempvar _t'32 tint) tint) tbool))))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'5 tint)
                          (Ssequence
                            (Sset _t'29
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                  (Tstruct _hs_snap noattr))
                                _last_initiation_consumption tulong))
                            (Ssequence
                              (Sset _t'30
                                (Efield
                                  (Ederef
                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                    (Tstruct _noise_handshake noattr))
                                  _last_initiation_consumption tulong))
                              (Sset _t'6
                                (Ecast
                                  (Ebinop Oeq (Etempvar _t'29 tulong)
                                    (Etempvar _t'30 tulong) tint) tbool))))
                          (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'6 tint)
                        (Ssequence
                          (Sset _t'27
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                (Tstruct _hs_snap noattr)) _static_identity
                              (tptr (Tstruct _noise_static_identity noattr))))
                          (Ssequence
                            (Sset _t'28
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                  (Tstruct _noise_handshake noattr))
                                _static_identity
                                (tptr (Tstruct _noise_static_identity noattr))))
                            (Sset _t'7
                              (Ecast
                                (Ebinop Oeq
                                  (Etempvar _t'27 (tptr (Tstruct _noise_static_identity noattr)))
                                  (Etempvar _t'28 (tptr (Tstruct _noise_static_identity noattr)))
                                  tint) tbool))))
                        (Sset _t'7 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'7 tint)
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _bytes_eq (Tfunction
                                            ((tptr tuchar) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tint cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                               (Tstruct _hs_snap noattr)) _ephemeral_private
                             (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _ephemeral_private (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Sset _t'8 (Ecast (Etempvar _t'9 tint) tbool)))
                      (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'8 tint)
                    (Ssequence
                      (Scall (Some _t'11)
                        (Evar _bytes_eq (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tint cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                             (Tstruct _hs_snap noattr)) _remote_static
                           (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _remote_static (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Sset _t'10 (Ecast (Etempvar _t'11 tint) tbool)))
                    (Sset _t'10 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'10 tint)
                  (Ssequence
                    (Scall (Some _t'13)
                      (Evar _bytes_eq (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tint cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                           (Tstruct _hs_snap noattr)) _remote_ephemeral
                         (tarray tuchar 32)) ::
                       (Efield
                         (Ederef
                           (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                           (Tstruct _noise_handshake noattr))
                         _remote_ephemeral (tarray tuchar 32)) ::
                       (Econst_int (Int.repr 32) tint) :: nil))
                    (Sset _t'12 (Ecast (Etempvar _t'13 tint) tbool)))
                  (Sset _t'12 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'12 tint)
                (Ssequence
                  (Scall (Some _t'15)
                    (Evar _bytes_eq (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tulong :: nil) tint cc_default))
                    ((Efield
                       (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                         (Tstruct _hs_snap noattr))
                       _precomputed_static_static (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr))
                       _precomputed_static_static (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Sset _t'14 (Ecast (Etempvar _t'15 tint) tbool)))
                (Sset _t'14 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'14 tint)
              (Ssequence
                (Scall (Some _t'17)
                  (Evar _bytes_eq (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tint cc_default))
                  ((Efield
                     (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                       (Tstruct _hs_snap noattr)) _preshared_key
                     (tarray tuchar 32)) ::
                   (Efield
                     (Ederef
                       (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                       (Tstruct _noise_handshake noattr)) _preshared_key
                     (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Sset _t'16 (Ecast (Etempvar _t'17 tint) tbool)))
              (Sset _t'16 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'16 tint)
            (Ssequence
              (Scall (Some _t'19)
                (Evar _bytes_eq (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tint cc_default))
                ((Efield
                   (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                     (Tstruct _hs_snap noattr)) _hash (tarray tuchar 32)) ::
                 (Efield
                   (Ederef
                     (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                     (Tstruct _noise_handshake noattr)) _hash
                   (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
                 nil))
              (Sset _t'18 (Ecast (Etempvar _t'19 tint) tbool)))
            (Sset _t'18 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'18 tint)
          (Ssequence
            (Scall (Some _t'21)
              (Evar _bytes_eq (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tint cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                   (Tstruct _hs_snap noattr)) _chaining_key
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef
                   (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _chaining_key
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))
            (Sset _t'20 (Ecast (Etempvar _t'21 tint) tbool)))
          (Sset _t'20 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'20 tint)
        (Ssequence
          (Scall (Some _t'23)
            (Evar _bytes_eq (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tint cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                 (Tstruct _hs_snap noattr)) _latest_timestamp
               (tarray tuchar 12)) ::
             (Efield
               (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                 (Tstruct _noise_handshake noattr)) _latest_timestamp
               (tarray tuchar 12)) :: (Econst_int (Int.repr 12) tint) :: nil))
          (Sset _t'22 (Ecast (Etempvar _t'23 tint) tbool)))
        (Sset _t'22 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'22 tint)
      (Ssequence
        (Sset _t'25
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
              (Tstruct _hs_snap noattr)) _remote_index tuint))
        (Ssequence
          (Sset _t'26
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _remote_index tuint))
          (Sset _t'24
            (Ecast
              (Ebinop Oeq (Etempvar _t'25 tuint) (Etempvar _t'26 tuint) tint)
              tbool))))
      (Sset _t'24 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'24 tint))))
|}.

Definition f_ck_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _ck_snap noattr))) ::
                (_c, (tptr (Tstruct _cookie noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tbool) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
          (Tstruct _cookie noattr)) _birthdate tulong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
          (Tstruct _ck_snap noattr)) _birthdate tulong)
      (Etempvar _t'3 tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
            (Tstruct _cookie noattr)) _is_valid tbool))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
            (Tstruct _ck_snap noattr)) _is_valid tbool)
        (Etempvar _t'2 tbool)))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
             (Tstruct _ck_snap noattr)) _cookie (tarray tuchar 16)) ::
         (Efield
           (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
             (Tstruct _cookie noattr)) _cookie (tarray tuchar 16)) ::
         (Econst_int (Int.repr 16) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                (Tstruct _cookie noattr)) _have_sent_mac1 tbool))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                (Tstruct _ck_snap noattr)) _have_sent_mac1 tbool)
            (Etempvar _t'1 tbool)))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                 (Tstruct _ck_snap noattr)) _last_mac1_sent
               (tarray tuchar 16)) ::
             (Efield
               (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                 (Tstruct _cookie noattr)) _last_mac1_sent
               (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                   (Tstruct _ck_snap noattr)) _cookie_decryption_key
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                   (Tstruct _cookie noattr)) _cookie_decryption_key
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                   (Tstruct _ck_snap noattr)) _message_mac1_key
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                   (Tstruct _cookie noattr)) _message_mac1_key
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))))))))
|}.

Definition f_ck_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _ck_snap noattr))) ::
                (_c, (tptr (Tstruct _cookie noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'16, tbool) :: (_t'15, tbool) ::
               (_t'14, tulong) :: (_t'13, tulong) :: (_t'12, tbool) ::
               (_t'11, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'13
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                    (Tstruct _ck_snap noattr)) _birthdate tulong))
              (Ssequence
                (Sset _t'14
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                      (Tstruct _cookie noattr)) _birthdate tulong))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'13 tulong)
                               (Etempvar _t'14 tulong) tint)
                  (Ssequence
                    (Sset _t'15
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                          (Tstruct _ck_snap noattr)) _is_valid tbool))
                    (Ssequence
                      (Sset _t'16
                        (Efield
                          (Ederef
                            (Etempvar _c (tptr (Tstruct _cookie noattr)))
                            (Tstruct _cookie noattr)) _is_valid tbool))
                      (Sset _t'1
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'15 tbool)
                            (Etempvar _t'16 tbool) tint) tbool))))
                  (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
            (Sifthenelse (Etempvar _t'1 tint)
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _bytes_eq (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tint cc_default))
                  ((Efield
                     (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                       (Tstruct _ck_snap noattr)) _cookie (tarray tuchar 16)) ::
                   (Efield
                     (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                       (Tstruct _cookie noattr)) _cookie (tarray tuchar 16)) ::
                   (Econst_int (Int.repr 16) tint) :: nil))
                (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
              (Sset _t'2 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'2 tint)
            (Ssequence
              (Sset _t'11
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                    (Tstruct _ck_snap noattr)) _have_sent_mac1 tbool))
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                      (Tstruct _cookie noattr)) _have_sent_mac1 tbool))
                (Sset _t'4
                  (Ecast
                    (Ebinop Oeq (Etempvar _t'11 tbool) (Etempvar _t'12 tbool)
                      tint) tbool))))
            (Sset _t'4 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'4 tint)
          (Ssequence
            (Scall (Some _t'6)
              (Evar _bytes_eq (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tint cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                   (Tstruct _ck_snap noattr)) _last_mac1_sent
                 (tarray tuchar 16)) ::
               (Efield
                 (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                   (Tstruct _cookie noattr)) _last_mac1_sent
                 (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) ::
               nil))
            (Sset _t'5 (Ecast (Etempvar _t'6 tint) tbool)))
          (Sset _t'5 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'5 tint)
        (Ssequence
          (Scall (Some _t'8)
            (Evar _bytes_eq (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tint cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
                 (Tstruct _ck_snap noattr)) _cookie_decryption_key
               (tarray tuchar 32)) ::
             (Efield
               (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
                 (Tstruct _cookie noattr)) _cookie_decryption_key
               (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Sset _t'7 (Ecast (Etempvar _t'8 tint) tbool)))
        (Sset _t'7 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'7 tint)
      (Ssequence
        (Scall (Some _t'10)
          (Evar _bytes_eq (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tint cc_default))
          ((Efield
             (Ederef (Etempvar _s (tptr (Tstruct _ck_snap noattr)))
               (Tstruct _ck_snap noattr)) _message_mac1_key
             (tarray tuchar 32)) ::
           (Efield
             (Ederef (Etempvar _c (tptr (Tstruct _cookie noattr)))
               (Tstruct _cookie noattr)) _message_mac1_key
             (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
        (Sset _t'9 (Ecast (Etempvar _t'10 tint) tbool)))
      (Sset _t'9 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'9 tint))))
|}.

Definition f_pr_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _pr_snap noattr))) ::
                (_p, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, (tptr (Tstruct _wg_device noattr))) :: (_t'7, tbool) ::
               (_t'6, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'5, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'4, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'3, tlong) :: (_t'2, tulong) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
          (Tstruct _wg_peer noattr)) _device
        (tptr (Tstruct _wg_device noattr))))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
          (Tstruct _pr_snap noattr)) _device
        (tptr (Tstruct _wg_device noattr)))
      (Etempvar _t'8 (tptr (Tstruct _wg_device noattr)))))
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
            (Tstruct _wg_peer noattr)) _is_dead tbool))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
            (Tstruct _pr_snap noattr)) _is_dead tbool) (Etempvar _t'7 tbool)))
    (Ssequence
      (Ssequence
        (Sset _t'6
          (Efield
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _keypairs
              (Tstruct _noise_keypairs noattr)) _current_keypair
            (tptr (Tstruct _noise_keypair noattr))))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
              (Tstruct _pr_snap noattr)) _current_keypair
            (tptr (Tstruct _noise_keypair noattr)))
          (Etempvar _t'6 (tptr (Tstruct _noise_keypair noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _keypairs
                (Tstruct _noise_keypairs noattr)) _previous_keypair
              (tptr (Tstruct _noise_keypair noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                (Tstruct _pr_snap noattr)) _previous_keypair
              (tptr (Tstruct _noise_keypair noattr)))
            (Etempvar _t'5 (tptr (Tstruct _noise_keypair noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Efield
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _keypairs
                  (Tstruct _noise_keypairs noattr)) _next_keypair
                (tptr (Tstruct _noise_keypair noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                  (Tstruct _pr_snap noattr)) _next_keypair
                (tptr (Tstruct _noise_keypair noattr)))
              (Etempvar _t'4 (tptr (Tstruct _noise_keypair noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'3
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _last_sent_handshake
                    (Tstruct ___gp_atomic64_t noattr)) _counter tlong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                    (Tstruct _pr_snap noattr)) _last_sent_handshake tlong)
                (Etempvar _t'3 tlong)))
            (Ssequence
              (Scall None
                (Evar _ck_take (Tfunction
                                 ((tptr (Tstruct _ck_snap noattr)) ::
                                  (tptr (Tstruct _cookie noattr)) :: nil)
                                 tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                       (Tstruct _pr_snap noattr)) _cookie
                     (Tstruct _ck_snap noattr))
                   (tptr (Tstruct _ck_snap noattr))) ::
                 (Eaddrof
                   (Efield
                     (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                       (Tstruct _wg_peer noattr)) _latest_cookie
                     (Tstruct _cookie noattr))
                   (tptr (Tstruct _cookie noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _internal_id tulong))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                        (Tstruct _pr_snap noattr)) _internal_id tulong)
                    (Etempvar _t'2 tulong)))
                (Ssequence
                  (Sset _t'1
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _pubkey_next
                      (tptr (Tstruct _wg_peer noattr))))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                        (Tstruct _pr_snap noattr)) _pubkey_next
                      (tptr (Tstruct _wg_peer noattr)))
                    (Etempvar _t'1 (tptr (Tstruct _wg_peer noattr)))))))))))))
|}.

Definition f_pr_same_but_cookie := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _pr_snap noattr))) ::
                (_p, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'23, tbool) :: (_t'22, tbool) ::
               (_t'21, (tptr (Tstruct _wg_device noattr))) ::
               (_t'20, (tptr (Tstruct _wg_device noattr))) ::
               (_t'19, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'18, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'17, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'16, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'15, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'14, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'13, tlong) :: (_t'12, tlong) :: (_t'11, tulong) ::
               (_t'10, tulong) :: (_t'9, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'8, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'20
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                      (Tstruct _pr_snap noattr)) _device
                    (tptr (Tstruct _wg_device noattr))))
                (Ssequence
                  (Sset _t'21
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _device
                      (tptr (Tstruct _wg_device noattr))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _t'20 (tptr (Tstruct _wg_device noattr)))
                                 (Etempvar _t'21 (tptr (Tstruct _wg_device noattr)))
                                 tint)
                    (Ssequence
                      (Sset _t'22
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                            (Tstruct _pr_snap noattr)) _is_dead tbool))
                      (Ssequence
                        (Sset _t'23
                          (Efield
                            (Ederef
                              (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _is_dead tbool))
                        (Sset _t'1
                          (Ecast
                            (Ebinop Oeq (Etempvar _t'22 tbool)
                              (Etempvar _t'23 tbool) tint) tbool))))
                    (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
              (Sifthenelse (Etempvar _t'1 tint)
                (Ssequence
                  (Sset _t'18
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                        (Tstruct _pr_snap noattr)) _current_keypair
                      (tptr (Tstruct _noise_keypair noattr))))
                  (Ssequence
                    (Sset _t'19
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _keypairs
                          (Tstruct _noise_keypairs noattr)) _current_keypair
                        (tptr (Tstruct _noise_keypair noattr))))
                    (Sset _t'2
                      (Ecast
                        (Ebinop Oeq
                          (Etempvar _t'18 (tptr (Tstruct _noise_keypair noattr)))
                          (Etempvar _t'19 (tptr (Tstruct _noise_keypair noattr)))
                          tint) tbool))))
                (Sset _t'2 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'2 tint)
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                      (Tstruct _pr_snap noattr)) _previous_keypair
                    (tptr (Tstruct _noise_keypair noattr))))
                (Ssequence
                  (Sset _t'17
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                          (Tstruct _wg_peer noattr)) _keypairs
                        (Tstruct _noise_keypairs noattr)) _previous_keypair
                      (tptr (Tstruct _noise_keypair noattr))))
                  (Sset _t'3
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _t'16 (tptr (Tstruct _noise_keypair noattr)))
                        (Etempvar _t'17 (tptr (Tstruct _noise_keypair noattr)))
                        tint) tbool))))
              (Sset _t'3 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Ssequence
              (Sset _t'14
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                    (Tstruct _pr_snap noattr)) _next_keypair
                  (tptr (Tstruct _noise_keypair noattr))))
              (Ssequence
                (Sset _t'15
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _keypairs
                      (Tstruct _noise_keypairs noattr)) _next_keypair
                    (tptr (Tstruct _noise_keypair noattr))))
                (Sset _t'4
                  (Ecast
                    (Ebinop Oeq
                      (Etempvar _t'14 (tptr (Tstruct _noise_keypair noattr)))
                      (Etempvar _t'15 (tptr (Tstruct _noise_keypair noattr)))
                      tint) tbool))))
            (Sset _t'4 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'4 tint)
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                  (Tstruct _pr_snap noattr)) _last_sent_handshake tlong))
            (Ssequence
              (Sset _t'13
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _last_sent_handshake
                    (Tstruct ___gp_atomic64_t noattr)) _counter tlong))
              (Sset _t'5
                (Ecast
                  (Ebinop Oeq (Etempvar _t'12 tlong) (Etempvar _t'13 tlong)
                    tint) tbool))))
          (Sset _t'5 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'5 tint)
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                (Tstruct _pr_snap noattr)) _internal_id tulong))
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _internal_id tulong))
            (Sset _t'6
              (Ecast
                (Ebinop Oeq (Etempvar _t'10 tulong) (Etempvar _t'11 tulong)
                  tint) tbool))))
        (Sset _t'6 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'6 tint)
      (Ssequence
        (Sset _t'8
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
              (Tstruct _pr_snap noattr)) _pubkey_next
            (tptr (Tstruct _wg_peer noattr))))
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _pubkey_next
              (tptr (Tstruct _wg_peer noattr))))
          (Sset _t'7
            (Ecast
              (Ebinop Oeq (Etempvar _t'8 (tptr (Tstruct _wg_peer noattr)))
                (Etempvar _t'9 (tptr (Tstruct _wg_peer noattr))) tint) tbool))))
      (Sset _t'7 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'7 tint))))
|}.

Definition f_pr_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _pr_snap noattr))) ::
                (_p, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _pr_same_but_cookie (Tfunction
                                  ((tptr (Tstruct _pr_snap noattr)) ::
                                   (tptr (Tstruct _wg_peer noattr)) :: nil)
                                  tint cc_default))
      ((Etempvar _s (tptr (Tstruct _pr_snap noattr))) ::
       (Etempvar _p (tptr (Tstruct _wg_peer noattr))) :: nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Ssequence
        (Scall (Some _t'3)
          (Evar _ck_same (Tfunction
                           ((tptr (Tstruct _ck_snap noattr)) ::
                            (tptr (Tstruct _cookie noattr)) :: nil) tint
                           cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _s (tptr (Tstruct _pr_snap noattr)))
                 (Tstruct _pr_snap noattr)) _cookie
               (Tstruct _ck_snap noattr)) (tptr (Tstruct _ck_snap noattr))) ::
           (Eaddrof
             (Efield
               (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                 (Tstruct _wg_peer noattr)) _latest_cookie
               (Tstruct _cookie noattr)) (tptr (Tstruct _cookie noattr))) ::
           nil))
        (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
      (Sset _t'2 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'2 tint))))
|}.

Definition f_cookie_img := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_img, (tptr tuchar)) ::
                (_m, (tptr (Tstruct _message_handshake_cookie noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Efield
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _header
          (Tstruct _message_header noattr)) _type tuint))
    (Scall None
      (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                          cc_default))
      ((Etempvar _img (tptr tuchar)) :: (Etempvar _t'2 tuint) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _receiver_index
          tuint))
      (Scall None
        (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                            cc_default))
        ((Ebinop Oadd (Etempvar _img (tptr tuchar))
           (Econst_int (Int.repr 4) tint) (tptr tuchar)) ::
         (Etempvar _t'1 tuint) :: nil)))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Ebinop Oadd (Etempvar _img (tptr tuchar))
           (Econst_int (Int.repr 8) tint) (tptr tuchar)) ::
         (Efield
           (Ederef
             (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
             (Tstruct _message_handshake_cookie noattr)) _nonce
           (tarray tuchar 24)) :: (Econst_int (Int.repr 24) tint) :: nil))
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Ebinop Oadd (Etempvar _img (tptr tuchar))
           (Econst_int (Int.repr 32) tint) (tptr tuchar)) ::
         (Efield
           (Ederef
             (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
             (Tstruct _message_handshake_cookie noattr)) _encrypted_cookie
           (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)))))
|}.

Definition f_fill_cookie_msg := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _message_handshake_cookie noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sassign
      (Efield
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _header
          (Tstruct _message_header noattr)) _type tuint)
      (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sassign
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _receiver_index
          tuint) (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Efield
           (Ederef
             (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
             (Tstruct _message_handshake_cookie noattr)) _nonce
           (tarray tuchar 24)) :: (Econst_int (Int.repr 24) tint) :: nil))
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Efield
           (Ederef
             (Etempvar _m (tptr (Tstruct _message_handshake_cookie noattr)))
             (Tstruct _message_handshake_cookie noattr)) _encrypted_cookie
           (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)))))
|}.

Definition f_draw_peer_refs := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'3, tuchar) :: (_t'2, tuint) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
  (Sswitch (Ebinop Omod (Etempvar _t'1 tuchar) (Econst_int (Int.repr 4) tint)
             tint)
    (LScons (Some 0)
      (Ssequence
        (Scall (Some _t'2)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                         (Ebinop Omod (Etempvar _t'2 tuint)
                           (Ebinop Osub
                             (Econst_int (Int.repr 2147483647) tuint)
                             (Econst_int (Int.repr 1) tint) tuint) tuint)
                         tuint))))
      (LScons (Some 1)
        (Sreturn (Some (Ebinop Osub (Econst_int (Int.repr 2147483647) tuint)
                         (Econst_int (Int.repr 1) tint) tuint)))
        (LScons None
          (Ssequence
            (Scall (Some _t'3)
              (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
            (Sreturn (Some (Ebinop Oadd (Econst_int (Int.repr 1) tint)
                             (Ebinop Oand (Etempvar _t'3 tuchar)
                               (Econst_int (Int.repr 1) tint) tint) tint))))
          LSnil)))))
|}.

Definition f_hnodes_snap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, (tptr (Tstruct _wg_peer noattr))) :: (_t'3, tuint) ::
               (_t'2, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Sifthenelse (Etempvar _l (tptr (Tstruct _hnode noattr))) Sskip Sbreak)
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
              (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr))))
        (Scall None
          (Evar _hs_take (Tfunction
                           ((tptr (Tstruct _hs_snap noattr)) ::
                            (tptr (Tstruct _noise_handshake noattr)) :: nil)
                           tvoid cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                 (Tstruct _hnode noattr)) _snap (Tstruct _hs_snap noattr))
             (tptr (Tstruct _hs_snap noattr))) ::
           (Eaddrof
             (Efield
               (Ederef (Etempvar _t'4 (tptr (Tstruct _wg_peer noattr)))
                 (Tstruct _wg_peer noattr)) _handshake
               (Tstruct _noise_handshake noattr))
             (tptr (Tstruct _noise_handshake noattr))) :: nil)))
      (Ssequence
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Efield
                  (Ederef (Etempvar _t'2 (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _refcount
                  (Tstruct _kref noattr)) _refcount tuint))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                  (Tstruct _hnode noattr)) _refs tuint)
              (Etempvar _t'3 tuint))))
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr))))
          (Scall None
            (Evar _pr_take (Tfunction
                             ((tptr (Tstruct _pr_snap noattr)) ::
                              (tptr (Tstruct _wg_peer noattr)) :: nil) tvoid
                             cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                   (Tstruct _hnode noattr)) _rest (Tstruct _pr_snap noattr))
               (tptr (Tstruct _pr_snap noattr))) ::
             (Etempvar _t'1 (tptr (Tstruct _wg_peer noattr))) :: nil))))))
  (Sset _l
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
        (Tstruct _hnode noattr)) _next (tptr (Tstruct _hnode noattr)))))
|}.

Definition f_hnodes_same_except := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _hnode noattr))) ::
                (_except, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'10, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'9, tuint) :: (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'6, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Sifthenelse (Etempvar _l (tptr (Tstruct _hnode noattr))) Sskip Sbreak)
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr))))
          (Sifthenelse (Ebinop One
                         (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))
                         (Etempvar _except (tptr (Tstruct _wg_peer noattr)))
                         tint)
            (Ssequence
              (Ssequence
                (Ssequence
                  (Sset _t'10
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                        (Tstruct _hnode noattr)) _p
                      (tptr (Tstruct _wg_peer noattr))))
                  (Scall (Some _t'2)
                    (Evar _hs_same (Tfunction
                                     ((tptr (Tstruct _hs_snap noattr)) ::
                                      (tptr (Tstruct _noise_handshake noattr)) ::
                                      nil) tint cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                           (Tstruct _hnode noattr)) _snap
                         (Tstruct _hs_snap noattr))
                       (tptr (Tstruct _hs_snap noattr))) ::
                     (Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _t'10 (tptr (Tstruct _wg_peer noattr)))
                           (Tstruct _wg_peer noattr)) _handshake
                         (Tstruct _noise_handshake noattr))
                       (tptr (Tstruct _noise_handshake noattr))) :: nil)))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                  (Sset _t'3 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'7
                      (Efield
                        (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                          (Tstruct _hnode noattr)) _p
                        (tptr (Tstruct _wg_peer noattr))))
                    (Ssequence
                      (Sset _t'8
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _t'7 (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _refcount
                            (Tstruct _kref noattr)) _refcount tuint))
                      (Ssequence
                        (Sset _t'9
                          (Efield
                            (Ederef
                              (Etempvar _l (tptr (Tstruct _hnode noattr)))
                              (Tstruct _hnode noattr)) _refs tuint))
                        (Sset _t'3
                          (Ecast
                            (Ebinop One (Etempvar _t'8 tuint)
                              (Etempvar _t'9 tuint) tint) tbool)))))))
              (Sifthenelse (Etempvar _t'3 tint)
                (Sset _t'1 (Ecast (Econst_int (Int.repr 1) tint) tbool))
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Efield
                          (Ederef
                            (Etempvar _l (tptr (Tstruct _hnode noattr)))
                            (Tstruct _hnode noattr)) _p
                          (tptr (Tstruct _wg_peer noattr))))
                      (Scall (Some _t'4)
                        (Evar _pr_same (Tfunction
                                         ((tptr (Tstruct _pr_snap noattr)) ::
                                          (tptr (Tstruct _wg_peer noattr)) ::
                                          nil) tint cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _l (tptr (Tstruct _hnode noattr)))
                               (Tstruct _hnode noattr)) _rest
                             (Tstruct _pr_snap noattr))
                           (tptr (Tstruct _pr_snap noattr))) ::
                         (Etempvar _t'6 (tptr (Tstruct _wg_peer noattr))) ::
                         nil)))
                    (Sset _t'1
                      (Ecast (Eunop Onotbool (Etempvar _t'4 tint) tint)
                        tbool)))
                  (Sset _t'1 (Ecast (Etempvar _t'1 tint) tbool)))))
            (Sset _t'1 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'1 tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)))
    (Sset _l
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
          (Tstruct _hnode noattr)) _next (tptr (Tstruct _hnode noattr)))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_hnodes_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, (tptr (Tstruct _hnode noattr))) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Swhile
  (Etempvar _l (tptr (Tstruct _hnode noattr)))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
          (Tstruct _hnode noattr)) _next (tptr (Tstruct _hnode noattr))))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
              (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr))))
        (Scall None
          (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                   cc_default))
          ((Etempvar _t'1 (tptr (Tstruct _wg_peer noattr))) :: nil)))
      (Ssequence
        (Scall None
          (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                   cc_default))
          ((Etempvar _l (tptr (Tstruct _hnode noattr))) :: nil))
        (Sset _l (Etempvar _n (tptr (Tstruct _hnode noattr))))))))
|}.

Definition f_hnodes_add := {|
  fn_return := (tptr (Tstruct _hnode noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (tptr (Tstruct _hnode noattr)))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) ::
                (_pub, (tptr tuchar)) :: (_id, tulong) :: nil);
  fn_vars := ((_psk, (tarray tuchar 32)) :: nil);
  fn_temps := ((_n, (tptr (Tstruct _hnode noattr))) ::
               (_it, (tptr (Tstruct _hnode noattr))) :: (_t'6, tuint) ::
               (_t'5, (tptr tvoid)) :: (_t'4, tuchar) ::
               (_t'3, (tptr tvoid)) :: (_t'2, (tptr tvoid)) ::
               (_t'1, tint) :: (_t'11, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'10, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'9, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'8, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'7, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _it
      (Ederef (Etempvar _l (tptr (tptr (Tstruct _hnode noattr))))
        (tptr (Tstruct _hnode noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _it (tptr (Tstruct _hnode noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _it (tptr (Tstruct _hnode noattr)))
                  (Tstruct _hnode noattr)) _p
                (tptr (Tstruct _wg_peer noattr))))
            (Scall (Some _t'1)
              (Evar _bytes_eq (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tint cc_default))
              ((Efield
                 (Efield
                   (Ederef (Etempvar _t'11 (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _handshake
                   (Tstruct _noise_handshake noattr)) _remote_static
                 (tarray tuchar 32)) :: (Etempvar _pub (tptr tuchar)) ::
               (Econst_int (Int.repr 32) tint) :: nil)))
          (Sifthenelse (Etempvar _t'1 tint)
            (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid))))
            Sskip)))
      (Sset _it
        (Efield
          (Ederef (Etempvar _it (tptr (Tstruct _hnode noattr)))
            (Tstruct _hnode noattr)) _next (tptr (Tstruct _hnode noattr))))))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                   cc_default))
        ((Esizeof (Tstruct _hnode noattr) tulong) :: nil))
      (Sset _n (Etempvar _t'2 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _n (tptr (Tstruct _hnode noattr)))
                     (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                     tint)
        (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
        Sskip)
      (Ssequence
        (Ssequence
          (Scall (Some _t'3)
            (Evar _quickproof_malloc (Tfunction (tulong :: nil) (tptr tvoid)
                                       cc_default))
            ((Esizeof (Tstruct _wg_peer noattr) tulong) :: nil))
          (Sassign
            (Efield
              (Ederef (Etempvar _n (tptr (Tstruct _hnode noattr)))
                (Tstruct _hnode noattr)) _p (tptr (Tstruct _wg_peer noattr)))
            (Etempvar _t'3 (tptr tvoid))))
        (Ssequence
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef (Etempvar _n (tptr (Tstruct _hnode noattr)))
                  (Tstruct _hnode noattr)) _p
                (tptr (Tstruct _wg_peer noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'10 (tptr (Tstruct _wg_peer noattr)))
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) tint)
              (Ssequence
                (Scall None
                  (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil)
                                           tvoid cc_default))
                  ((Etempvar _n (tptr (Tstruct _hnode noattr))) :: nil))
                (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)))))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Evar _psk (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Ssequence
                (Ssequence
                  (Scall (Some _t'4)
                    (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
                  (Sifthenelse (Ebinop Oand (Etempvar _t'4 tuchar)
                                 (Econst_int (Int.repr 1) tint) tint)
                    (Sset _t'5
                      (Ecast (Evar _psk (tarray tuchar 32)) (tptr tvoid)))
                    (Sset _t'5
                      (Ecast
                        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                        (tptr tvoid)))))
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef (Etempvar _n (tptr (Tstruct _hnode noattr)))
                        (Tstruct _hnode noattr)) _p
                      (tptr (Tstruct _wg_peer noattr))))
                  (Scall None
                    (Evar _setup_peer (Tfunction
                                        ((tptr (Tstruct _wg_peer noattr)) ::
                                         (tptr (Tstruct _wg_device noattr)) ::
                                         (tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tvoid cc_default))
                    ((Etempvar _t'9 (tptr (Tstruct _wg_peer noattr))) ::
                     (Etempvar _wg (tptr (Tstruct _wg_device noattr))) ::
                     (Etempvar _pub (tptr tuchar)) ::
                     (Etempvar _t'5 (tptr tvoid)) :: (Etempvar _id tulong) ::
                     nil))))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'6)
                    (Evar _draw_peer_refs (Tfunction nil tuint cc_default))
                    nil)
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef (Etempvar _n (tptr (Tstruct _hnode noattr)))
                          (Tstruct _hnode noattr)) _p
                        (tptr (Tstruct _wg_peer noattr))))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _t'8 (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _refcount
                          (Tstruct _kref noattr)) _refcount tuint)
                      (Etempvar _t'6 tuint))))
                (Ssequence
                  (Ssequence
                    (Sset _t'7
                      (Ederef
                        (Etempvar _l (tptr (tptr (Tstruct _hnode noattr))))
                        (tptr (Tstruct _hnode noattr))))
                    (Sassign
                      (Efield
                        (Ederef (Etempvar _n (tptr (Tstruct _hnode noattr)))
                          (Tstruct _hnode noattr)) _next
                        (tptr (Tstruct _hnode noattr)))
                      (Etempvar _t'7 (tptr (Tstruct _hnode noattr)))))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Etempvar _l (tptr (tptr (Tstruct _hnode noattr))))
                        (tptr (Tstruct _hnode noattr)))
                      (Etempvar _n (tptr (Tstruct _hnode noattr))))
                    (Sreturn (Some (Etempvar _n (tptr (Tstruct _hnode noattr)))))))))))))))
|}.

Definition f_peer_randomize_rest := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tuchar) :: (_t'4, tulong) :: (_t'3, tuchar) ::
               (_t'2, tulong) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
      nil)
    (Sassign
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
          (Tstruct _wg_peer noattr)) _is_dead tbool)
      (Ebinop Oand (Etempvar _t'1 tuchar) (Econst_int (Int.repr 1) tint)
        tint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _draw_u64 (Tfunction nil tulong cc_default))
        nil)
      (Sassign
        (Efield
          (Efield
            (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
              (Tstruct _wg_peer noattr)) _last_sent_handshake
            (Tstruct ___gp_atomic64_t noattr)) _counter tlong)
        (Ecast (Etempvar _t'2 tulong) tlong)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _latest_cookie
              (Tstruct _cookie noattr)) _is_valid tbool)
          (Ebinop Oand (Etempvar _t'3 tuchar) (Econst_int (Int.repr 1) tint)
            tint)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'4)
            (Evar _draw_boottime (Tfunction nil tulong cc_default)) nil)
          (Sassign
            (Efield
              (Efield
                (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _latest_cookie
                (Tstruct _cookie noattr)) _birthdate tulong)
            (Etempvar _t'4 tulong)))
        (Ssequence
          (Scall None
            (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
            ((Efield
               (Efield
                 (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                   (Tstruct _wg_peer noattr)) _latest_cookie
                 (Tstruct _cookie noattr)) _cookie (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'5)
                (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
              (Sassign
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _latest_cookie
                    (Tstruct _cookie noattr)) _have_sent_mac1 tbool)
                (Ebinop Oand (Etempvar _t'5 tuchar)
                  (Econst_int (Int.repr 1) tint) tint)))
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _latest_cookie
                   (Tstruct _cookie noattr)) _last_mac1_sent
                 (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) ::
               nil))))))))
|}.

Definition f_hnodes_pick := {|
  fn_return := (tptr (Tstruct _hnode noattr));
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_k, tulong) :: (_t'2, tint) :: (_t'1, tulong) ::
               (_t'3, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_size (Tfunction nil tulong cc_default))
      nil)
    (Sset _k (Etempvar _t'1 tulong)))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Ogt (Etempvar _k tulong)
                         (Econst_int (Int.repr 0) tint) tint)
            (Ssequence
              (Sset _t'3
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                    (Tstruct _hnode noattr)) _next
                  (tptr (Tstruct _hnode noattr))))
              (Sset _t'2
                (Ecast
                  (Ebinop One (Etempvar _t'3 (tptr (Tstruct _hnode noattr)))
                    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
                  tbool)))
            (Sset _t'2 (Econst_int (Int.repr 0) tint)))
          (Sifthenelse (Etempvar _t'2 tint) Sskip Sbreak))
        (Ssequence
          (Sset _l
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _hnode noattr)))
                (Tstruct _hnode noattr)) _next
              (tptr (Tstruct _hnode noattr))))
          (Sset _k
            (Ebinop Osub (Etempvar _k tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      Sskip)
    (Sreturn (Some (Etempvar _l (tptr (Tstruct _hnode noattr)))))))
|}.

Definition f_dev_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _dev_snap noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, (tptr (Tstruct _net_device noattr))) ::
               (_t'7, tbool) :: (_t'6, tulong) ::
               (_t'5, (tptr (Tstruct _wg_device noattr))) ::
               (_t'4, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'3, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'2, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'1, (tptr (Tstruct _pubkey_hashtable noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
          (Tstruct _wg_device noattr)) _dev
        (tptr (Tstruct _net_device noattr))))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
          (Tstruct _dev_snap noattr)) _dev
        (tptr (Tstruct _net_device noattr)))
      (Etempvar _t'8 (tptr (Tstruct _net_device noattr)))))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
           (Tstruct _dev_snap noattr)) _static_public (tarray tuchar 32)) ::
       (Efield
         (Efield
           (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
             (Tstruct _wg_device noattr)) _static_identity
           (Tstruct _noise_static_identity noattr)) _static_public
         (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
             (Tstruct _dev_snap noattr)) _static_private (tarray tuchar 32)) ::
         (Efield
           (Efield
             (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
               (Tstruct _wg_device noattr)) _static_identity
             (Tstruct _noise_static_identity noattr)) _static_private
           (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Ssequence
          (Sset _t'7
            (Efield
              (Efield
                (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                  (Tstruct _wg_device noattr)) _static_identity
                (Tstruct _noise_static_identity noattr)) _has_identity tbool))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                (Tstruct _dev_snap noattr)) _has_identity tbool)
            (Etempvar _t'7 tbool)))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                 (Tstruct _dev_snap noattr)) _secret (tarray tuchar 32)) ::
             (Efield
               (Efield
                 (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                   (Tstruct _wg_device noattr)) _cookie_checker
                 (Tstruct _cookie_checker noattr)) _secret
               (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Ssequence
              (Sset _t'6
                (Efield
                  (Efield
                    (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                      (Tstruct _wg_device noattr)) _cookie_checker
                    (Tstruct _cookie_checker noattr)) _secret_birthdate
                  tulong))
              (Sassign
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                    (Tstruct _dev_snap noattr)) _secret_birthdate tulong)
                (Etempvar _t'6 tulong)))
            (Ssequence
              (Scall None
                (Evar _bytes_copy (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tvoid cc_default))
                ((Efield
                   (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                     (Tstruct _dev_snap noattr)) _cookie_encryption_key
                   (tarray tuchar 32)) ::
                 (Efield
                   (Efield
                     (Ederef
                       (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                       (Tstruct _wg_device noattr)) _cookie_checker
                     (Tstruct _cookie_checker noattr)) _cookie_encryption_key
                   (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
                 nil))
              (Ssequence
                (Scall None
                  (Evar _bytes_copy (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tulong :: nil) tvoid cc_default))
                  ((Efield
                     (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                       (Tstruct _dev_snap noattr)) _message_mac1_key
                     (tarray tuchar 32)) ::
                   (Efield
                     (Efield
                       (Ederef
                         (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                         (Tstruct _wg_device noattr)) _cookie_checker
                       (Tstruct _cookie_checker noattr)) _message_mac1_key
                     (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Ssequence
                  (Ssequence
                    (Sset _t'5
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                            (Tstruct _wg_device noattr)) _cookie_checker
                          (Tstruct _cookie_checker noattr)) _device
                        (tptr (Tstruct _wg_device noattr))))
                    (Sassign
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                          (Tstruct _dev_snap noattr)) _checker_device
                        (tptr (Tstruct _wg_device noattr)))
                      (Etempvar _t'5 (tptr (Tstruct _wg_device noattr)))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                            (Tstruct _wg_device noattr)) _peer_hashtable
                          (tptr (Tstruct _pubkey_hashtable noattr))))
                      (Sassign
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                            (Tstruct _dev_snap noattr)) _peer_hashtable
                          (tptr (Tstruct _pubkey_hashtable noattr)))
                        (Etempvar _t'4 (tptr (Tstruct _pubkey_hashtable noattr)))))
                    (Ssequence
                      (Ssequence
                        (Sset _t'3
                          (Efield
                            (Ederef
                              (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                              (Tstruct _wg_device noattr)) _index_hashtable
                            (tptr (Tstruct _index_hashtable noattr))))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                              (Tstruct _dev_snap noattr)) _index_hashtable
                            (tptr (Tstruct _index_hashtable noattr)))
                          (Etempvar _t'3 (tptr (Tstruct _index_hashtable noattr)))))
                      (Ssequence
                        (Sset _t'1
                          (Efield
                            (Ederef
                              (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                              (Tstruct _wg_device noattr)) _peer_hashtable
                            (tptr (Tstruct _pubkey_hashtable noattr))))
                        (Ssequence
                          (Sset _t'2
                            (Efield
                              (Ederef
                                (Etempvar _t'1 (tptr (Tstruct _pubkey_hashtable noattr)))
                                (Tstruct _pubkey_hashtable noattr)) _head
                              (tptr (Tstruct _wg_peer noattr))))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                                (Tstruct _dev_snap noattr)) _peers_head
                              (tptr (Tstruct _wg_peer noattr)))
                            (Etempvar _t'2 (tptr (Tstruct _wg_peer noattr)))))))))))))))))
|}.

Definition f_dev_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _dev_snap noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'16, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) ::
               (_t'31, (tptr (Tstruct _net_device noattr))) ::
               (_t'30, (tptr (Tstruct _net_device noattr))) ::
               (_t'29, tbool) :: (_t'28, tbool) :: (_t'27, tulong) ::
               (_t'26, tulong) ::
               (_t'25, (tptr (Tstruct _wg_device noattr))) ::
               (_t'24, (tptr (Tstruct _wg_device noattr))) ::
               (_t'23, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'22, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'21, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'20, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'19, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'18, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'17, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'30
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                              (Tstruct _dev_snap noattr)) _dev
                            (tptr (Tstruct _net_device noattr))))
                        (Ssequence
                          (Sset _t'31
                            (Efield
                              (Ederef
                                (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                (Tstruct _wg_device noattr)) _dev
                              (tptr (Tstruct _net_device noattr))))
                          (Sifthenelse (Ebinop Oeq
                                         (Etempvar _t'30 (tptr (Tstruct _net_device noattr)))
                                         (Etempvar _t'31 (tptr (Tstruct _net_device noattr)))
                                         tint)
                            (Ssequence
                              (Scall (Some _t'2)
                                (Evar _bytes_eq (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   nil) tint cc_default))
                                ((Efield
                                   (Ederef
                                     (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                                     (Tstruct _dev_snap noattr))
                                   _static_public (tarray tuchar 32)) ::
                                 (Efield
                                   (Efield
                                     (Ederef
                                       (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                       (Tstruct _wg_device noattr))
                                     _static_identity
                                     (Tstruct _noise_static_identity noattr))
                                   _static_public (tarray tuchar 32)) ::
                                 (Econst_int (Int.repr 32) tint) :: nil))
                              (Sset _t'1 (Ecast (Etempvar _t'2 tint) tbool)))
                            (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
                      (Sifthenelse (Etempvar _t'1 tint)
                        (Ssequence
                          (Scall (Some _t'4)
                            (Evar _bytes_eq (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tint cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                                 (Tstruct _dev_snap noattr)) _static_private
                               (tarray tuchar 32)) ::
                             (Efield
                               (Efield
                                 (Ederef
                                   (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                   (Tstruct _wg_device noattr))
                                 _static_identity
                                 (Tstruct _noise_static_identity noattr))
                               _static_private (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Sset _t'3 (Ecast (Etempvar _t'4 tint) tbool)))
                        (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'3 tint)
                      (Ssequence
                        (Sset _t'28
                          (Efield
                            (Ederef
                              (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                              (Tstruct _dev_snap noattr)) _has_identity
                            tbool))
                        (Ssequence
                          (Sset _t'29
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                  (Tstruct _wg_device noattr))
                                _static_identity
                                (Tstruct _noise_static_identity noattr))
                              _has_identity tbool))
                          (Sset _t'5
                            (Ecast
                              (Ebinop Oeq (Etempvar _t'28 tbool)
                                (Etempvar _t'29 tbool) tint) tbool))))
                      (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'5 tint)
                    (Ssequence
                      (Scall (Some _t'7)
                        (Evar _bytes_eq (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tint cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                             (Tstruct _dev_snap noattr)) _secret
                           (tarray tuchar 32)) ::
                         (Efield
                           (Efield
                             (Ederef
                               (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                               (Tstruct _wg_device noattr)) _cookie_checker
                             (Tstruct _cookie_checker noattr)) _secret
                           (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool)))
                    (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'6 tint)
                  (Ssequence
                    (Sset _t'26
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                          (Tstruct _dev_snap noattr)) _secret_birthdate
                        tulong))
                    (Ssequence
                      (Sset _t'27
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                              (Tstruct _wg_device noattr)) _cookie_checker
                            (Tstruct _cookie_checker noattr))
                          _secret_birthdate tulong))
                      (Sset _t'8
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'26 tulong)
                            (Etempvar _t'27 tulong) tint) tbool))))
                  (Sset _t'8 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'8 tint)
                (Ssequence
                  (Scall (Some _t'10)
                    (Evar _bytes_eq (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tulong :: nil) tint cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                         (Tstruct _dev_snap noattr)) _cookie_encryption_key
                       (tarray tuchar 32)) ::
                     (Efield
                       (Efield
                         (Ederef
                           (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                           (Tstruct _wg_device noattr)) _cookie_checker
                         (Tstruct _cookie_checker noattr))
                       _cookie_encryption_key (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Sset _t'9 (Ecast (Etempvar _t'10 tint) tbool)))
                (Sset _t'9 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'9 tint)
              (Ssequence
                (Scall (Some _t'12)
                  (Evar _bytes_eq (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tint cc_default))
                  ((Efield
                     (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                       (Tstruct _dev_snap noattr)) _message_mac1_key
                     (tarray tuchar 32)) ::
                   (Efield
                     (Efield
                       (Ederef
                         (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                         (Tstruct _wg_device noattr)) _cookie_checker
                       (Tstruct _cookie_checker noattr)) _message_mac1_key
                     (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Sset _t'11 (Ecast (Etempvar _t'12 tint) tbool)))
              (Sset _t'11 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'11 tint)
            (Ssequence
              (Sset _t'24
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                    (Tstruct _dev_snap noattr)) _checker_device
                  (tptr (Tstruct _wg_device noattr))))
              (Ssequence
                (Sset _t'25
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                        (Tstruct _wg_device noattr)) _cookie_checker
                      (Tstruct _cookie_checker noattr)) _device
                    (tptr (Tstruct _wg_device noattr))))
                (Sset _t'13
                  (Ecast
                    (Ebinop Oeq
                      (Etempvar _t'24 (tptr (Tstruct _wg_device noattr)))
                      (Etempvar _t'25 (tptr (Tstruct _wg_device noattr)))
                      tint) tbool))))
            (Sset _t'13 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'13 tint)
          (Ssequence
            (Sset _t'22
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                  (Tstruct _dev_snap noattr)) _peer_hashtable
                (tptr (Tstruct _pubkey_hashtable noattr))))
            (Ssequence
              (Sset _t'23
                (Efield
                  (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                    (Tstruct _wg_device noattr)) _peer_hashtable
                  (tptr (Tstruct _pubkey_hashtable noattr))))
              (Sset _t'14
                (Ecast
                  (Ebinop Oeq
                    (Etempvar _t'22 (tptr (Tstruct _pubkey_hashtable noattr)))
                    (Etempvar _t'23 (tptr (Tstruct _pubkey_hashtable noattr)))
                    tint) tbool))))
          (Sset _t'14 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'14 tint)
        (Ssequence
          (Sset _t'20
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
                (Tstruct _dev_snap noattr)) _index_hashtable
              (tptr (Tstruct _index_hashtable noattr))))
          (Ssequence
            (Sset _t'21
              (Efield
                (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                  (Tstruct _wg_device noattr)) _index_hashtable
                (tptr (Tstruct _index_hashtable noattr))))
            (Sset _t'15
              (Ecast
                (Ebinop Oeq
                  (Etempvar _t'20 (tptr (Tstruct _index_hashtable noattr)))
                  (Etempvar _t'21 (tptr (Tstruct _index_hashtable noattr)))
                  tint) tbool))))
        (Sset _t'15 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'15 tint)
      (Ssequence
        (Sset _t'17
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _dev_snap noattr)))
              (Tstruct _dev_snap noattr)) _peers_head
            (tptr (Tstruct _wg_peer noattr))))
        (Ssequence
          (Sset _t'18
            (Efield
              (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                (Tstruct _wg_device noattr)) _peer_hashtable
              (tptr (Tstruct _pubkey_hashtable noattr))))
          (Ssequence
            (Sset _t'19
              (Efield
                (Ederef
                  (Etempvar _t'18 (tptr (Tstruct _pubkey_hashtable noattr)))
                  (Tstruct _pubkey_hashtable noattr)) _head
                (tptr (Tstruct _wg_peer noattr))))
            (Sset _t'16
              (Ecast
                (Ebinop Oeq (Etempvar _t'17 (tptr (Tstruct _wg_peer noattr)))
                  (Etempvar _t'19 (tptr (Tstruct _wg_peer noattr))) tint)
                tbool)))))
      (Sset _t'16 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'16 tint))))
|}.

Definition f_shim_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _shim_snap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'5, tulong) :: (_t'4, tulong) ::
               (_t'3, tulong) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5 (Evar _wg_shim_allocs tulong))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
          (Tstruct _shim_snap noattr)) _allocs tulong)
      (Etempvar _t'5 tulong)))
  (Ssequence
    (Ssequence
      (Sset _t'4 (Evar _wg_shim_alloc_failures tulong))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
            (Tstruct _shim_snap noattr)) _alloc_failures tulong)
        (Etempvar _t'4 tulong)))
    (Ssequence
      (Ssequence
        (Sset _t'3 (Evar _wg_shim_frees tulong))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
              (Tstruct _shim_snap noattr)) _frees tulong)
          (Etempvar _t'3 tulong)))
      (Ssequence
        (Ssequence
          (Sset _t'2 (Evar _wg_shim_peer_released tulong))
          (Sassign
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                (Tstruct _shim_snap noattr)) _peer_released tulong)
            (Etempvar _t'2 tulong)))
        (Ssequence
          (Sset _i (Econst_int (Int.repr 0) tint))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 5) tint) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd
                      (Evar _wg_shim_refcount_warn (tarray tulong 5))
                      (Etempvar _i tint) (tptr tulong)) tulong))
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                          (Tstruct _shim_snap noattr)) _refcount_warn
                        (tarray tulong 5)) (Etempvar _i tint) (tptr tulong))
                    tulong) (Etempvar _t'1 tulong))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
                tint))))))))
|}.

Definition f_shim_no_warning := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _shim_snap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 5) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                    (Tstruct _shim_snap noattr)) _refcount_warn
                  (tarray tulong 5)) (Etempvar _i tint) (tptr tulong))
              tulong))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Evar _wg_shim_refcount_warn (tarray tulong 5))
                  (Etempvar _i tint) (tptr tulong)) tulong))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tulong)
                           (Etempvar _t'2 tulong) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_shim_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _shim_snap noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'13, tulong) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tulong) ::
               (_t'9, tulong) :: (_t'8, tulong) :: (_t'7, tulong) ::
               (_t'6, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'10
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                (Tstruct _shim_snap noattr)) _allocs tulong))
          (Ssequence
            (Sset _t'11 (Evar _wg_shim_allocs tulong))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'10 tulong)
                           (Etempvar _t'11 tulong) tint)
              (Ssequence
                (Sset _t'12
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                      (Tstruct _shim_snap noattr)) _alloc_failures tulong))
                (Ssequence
                  (Sset _t'13 (Evar _wg_shim_alloc_failures tulong))
                  (Sset _t'1
                    (Ecast
                      (Ebinop Oeq (Etempvar _t'12 tulong)
                        (Etempvar _t'13 tulong) tint) tbool))))
              (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
        (Sifthenelse (Etempvar _t'1 tint)
          (Ssequence
            (Sset _t'8
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                  (Tstruct _shim_snap noattr)) _frees tulong))
            (Ssequence
              (Sset _t'9 (Evar _wg_shim_frees tulong))
              (Sset _t'2
                (Ecast
                  (Ebinop Oeq (Etempvar _t'8 tulong) (Etempvar _t'9 tulong)
                    tint) tbool))))
          (Sset _t'2 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'2 tint)
        (Ssequence
          (Sset _t'6
            (Efield
              (Ederef (Etempvar _s (tptr (Tstruct _shim_snap noattr)))
                (Tstruct _shim_snap noattr)) _peer_released tulong))
          (Ssequence
            (Sset _t'7 (Evar _wg_shim_peer_released tulong))
            (Sset _t'3
              (Ecast
                (Ebinop Oeq (Etempvar _t'6 tulong) (Etempvar _t'7 tulong)
                  tint) tbool))))
        (Sset _t'3 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'3 tint)
      (Ssequence
        (Scall (Some _t'5)
          (Evar _shim_no_warning (Tfunction
                                   ((tptr (Tstruct _shim_snap noattr)) ::
                                    nil) tint cc_default))
          ((Etempvar _s (tptr (Tstruct _shim_snap noattr))) :: nil))
        (Sset _t'4 (Ecast (Etempvar _t'5 tint) tbool)))
      (Sset _t'4 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'4 tint))))
|}.

Definition f_kents_add := {|
  fn_return := (tptr (Tstruct _kent noattr));
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _index_hashtable noattr))) ::
                (_peers, (tptr (Tstruct _hnode noattr))) ::
                (_p, (tptr (Tstruct _wg_peer noattr))) :: (_fill, tint) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_l, (tptr (Tstruct _kent noattr))) ::
               (_k, (tptr (Tstruct _kent noattr))) :: (_n, tulong) ::
               (_i, tulong) :: (_j, tulong) ::
               (_owner, (tptr (Tstruct _wg_peer noattr))) ::
               (_kp, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'18, tuchar) :: (_t'17, tulong) :: (_t'16, tuint) ::
               (_t'15, tuchar) :: (_t'14, tuint) :: (_t'13, tulong) ::
               (_t'12, tulong) :: (_t'11, tulong) :: (_t'10, tuchar) ::
               (_t'9, tulong) :: (_t'8, tuchar) :: (_t'7, tulong) ::
               (_t'6, (tptr (Tstruct _hnode noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'4, (tptr tvoid)) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tint) :: (_t'22, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'21, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'20, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'19, (tptr (Tstruct _noise_keypair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _l (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sifthenelse (Ebinop One
                       (Etempvar _peers (tptr (Tstruct _hnode noattr)))
                       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))
                       tint)
          (Sset _t'1 (Econst_int (Int.repr 1) tint))
          (Sset _t'1
            (Ecast
              (Ebinop One (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) tint)
              tbool)))
        (Sifthenelse (Etempvar _t'1 tint)
          (Ssequence
            (Scall (Some _t'3)
              (Evar _draw_steps (Tfunction nil tulong cc_default)) nil)
            (Sset _t'2 (Ecast (Etempvar _t'3 tulong) tulong)))
          (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tulong))))
      (Sset _n (Etempvar _t'2 tulong)))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Etempvar _n tulong) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _quickproof_malloc (Tfunction (tulong :: nil)
                                             (tptr tvoid) cc_default))
                  ((Esizeof (Tstruct _kent noattr) tulong) :: nil))
                (Sset _k (Etempvar _t'4 (tptr tvoid))))
              (Ssequence
                (Sifthenelse (Ebinop Oeq
                               (Etempvar _k (tptr (Tstruct _kent noattr)))
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr tvoid)) tint)
                  Sbreak
                  Sskip)
                (Ssequence
                  (Sset _kp
                    (Eaddrof
                      (Efield
                        (Ederef (Etempvar _k (tptr (Tstruct _kent noattr)))
                          (Tstruct _kent noattr)) _kp
                        (Tstruct _noise_keypair noattr))
                      (tptr (Tstruct _noise_keypair noattr))))
                  (Ssequence
                    (Ssequence
                      (Sifthenelse (Ebinop One
                                     (Etempvar _peers (tptr (Tstruct _hnode noattr)))
                                     (Ecast (Econst_int (Int.repr 0) tint)
                                       (tptr tvoid)) tint)
                        (Ssequence
                          (Scall (Some _t'6)
                            (Evar _hnodes_pick (Tfunction
                                                 ((tptr (Tstruct _hnode noattr)) ::
                                                  nil)
                                                 (tptr (Tstruct _hnode noattr))
                                                 cc_default))
                            ((Etempvar _peers (tptr (Tstruct _hnode noattr))) ::
                             nil))
                          (Ssequence
                            (Sset _t'22
                              (Efield
                                (Ederef
                                  (Etempvar _t'6 (tptr (Tstruct _hnode noattr)))
                                  (Tstruct _hnode noattr)) _p
                                (tptr (Tstruct _wg_peer noattr))))
                            (Sset _t'5
                              (Ecast
                                (Etempvar _t'22 (tptr (Tstruct _wg_peer noattr)))
                                (tptr (Tstruct _wg_peer noattr))))))
                        (Sset _t'5
                          (Ecast
                            (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                            (tptr (Tstruct _wg_peer noattr)))))
                      (Sset _owner
                        (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))))
                    (Ssequence
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                              (Tstruct _noise_keypair noattr)) _entry
                            (Tstruct _index_hashtable_entry noattr)) _peer
                          (tptr (Tstruct _wg_peer noattr)))
                        (Etempvar _owner (tptr (Tstruct _wg_peer noattr))))
                      (Ssequence
                        (Sassign
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                (Tstruct _noise_keypair noattr)) _entry
                              (Tstruct _index_hashtable_entry noattr)) _type
                            tint) (Econst_int (Int.repr 2) tint))
                        (Ssequence
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                  (Tstruct _noise_keypair noattr)) _entry
                                (Tstruct _index_hashtable_entry noattr))
                              _next
                              (tptr (Tstruct _index_hashtable_entry noattr)))
                            (Ecast (Econst_int (Int.repr 0) tint)
                              (tptr tvoid)))
                          (Ssequence
                            (Sassign
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                    (Tstruct _noise_keypair noattr)) _entry
                                  (Tstruct _index_hashtable_entry noattr))
                                _hashed tbool)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Scall None
                                (Evar _wg_index_hashtable_insert (Tfunction
                                                                   ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil)
                                                                   tuint
                                                                   cc_default))
                                ((Etempvar _t (tptr (Tstruct _index_hashtable noattr))) ::
                                 (Eaddrof
                                   (Efield
                                     (Ederef
                                       (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                       (Tstruct _noise_keypair noattr))
                                     _entry
                                     (Tstruct _index_hashtable_entry noattr))
                                   (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                 nil))
                              (Ssequence
                                (Scall None
                                  (Evar _nondet_bytes (Tfunction
                                                        ((tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                  ((Efield
                                     (Efield
                                       (Ederef
                                         (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                         (Tstruct _noise_keypair noattr))
                                       _sending
                                       (Tstruct _noise_symmetric_key noattr))
                                     _key (tarray tuchar 32)) ::
                                   (Econst_int (Int.repr 32) tint) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'7)
                                      (Evar _draw_boottime (Tfunction nil
                                                             tulong
                                                             cc_default))
                                      nil)
                                    (Sassign
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                            (Tstruct _noise_keypair noattr))
                                          _sending
                                          (Tstruct _noise_symmetric_key noattr))
                                        _birthdate tulong)
                                      (Etempvar _t'7 tulong)))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'8)
                                        (Evar _nondet_u8 (Tfunction nil
                                                           tuchar cc_default))
                                        nil)
                                      (Sassign
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                              (Tstruct _noise_keypair noattr))
                                            _sending
                                            (Tstruct _noise_symmetric_key noattr))
                                          _is_valid tbool)
                                        (Ebinop Oand (Etempvar _t'8 tuchar)
                                          (Econst_int (Int.repr 1) tint)
                                          tint)))
                                    (Ssequence
                                      (Scall None
                                        (Evar _nondet_bytes (Tfunction
                                                              ((tptr tuchar) ::
                                                               tulong :: nil)
                                                              tvoid
                                                              cc_default))
                                        ((Efield
                                           (Efield
                                             (Ederef
                                               (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                               (Tstruct _noise_keypair noattr))
                                             _receiving
                                             (Tstruct _noise_symmetric_key noattr))
                                           _key (tarray tuchar 32)) ::
                                         (Econst_int (Int.repr 32) tint) ::
                                         nil))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'9)
                                            (Evar _draw_boottime (Tfunction
                                                                   nil tulong
                                                                   cc_default))
                                            nil)
                                          (Sassign
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                  (Tstruct _noise_keypair noattr))
                                                _receiving
                                                (Tstruct _noise_symmetric_key noattr))
                                              _birthdate tulong)
                                            (Etempvar _t'9 tulong)))
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'10)
                                              (Evar _nondet_u8 (Tfunction nil
                                                                 tuchar
                                                                 cc_default))
                                              nil)
                                            (Sassign
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                    (Tstruct _noise_keypair noattr))
                                                  _receiving
                                                  (Tstruct _noise_symmetric_key noattr))
                                                _is_valid tbool)
                                              (Ebinop Oand
                                                (Etempvar _t'10 tuchar)
                                                (Econst_int (Int.repr 1) tint)
                                                tint)))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'11)
                                                (Evar _draw_u64 (Tfunction
                                                                  nil tulong
                                                                  cc_default))
                                                nil)
                                              (Sassign
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                      (Tstruct _noise_keypair noattr))
                                                    _sending_counter
                                                    (Tstruct ___gp_atomic64_t noattr))
                                                  _counter tlong)
                                                (Ecast
                                                  (Etempvar _t'11 tulong)
                                                  tlong)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'12)
                                                  (Evar _draw_u64 (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                  nil)
                                                (Sassign
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                        (Tstruct _noise_keypair noattr))
                                                      _receiving_counter
                                                      (Tstruct _noise_replay_counter noattr))
                                                    _counter tulong)
                                                  (Etempvar _t'12 tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _j
                                                    (Ecast
                                                      (Econst_int (Int.repr 0) tint)
                                                      tulong))
                                                  (Sloop
                                                    (Ssequence
                                                      (Sifthenelse (Ebinop Olt
                                                                    (Etempvar _j tulong)
                                                                    (Ebinop Odiv
                                                                    (Econst_int (Int.repr 8192) tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tint)
                                                        Sskip
                                                        Sbreak)
                                                      (Ssequence
                                                        (Scall (Some _t'13)
                                                          (Evar _draw_u64 
                                                          (Tfunction nil
                                                            tulong
                                                            cc_default)) nil)
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Efield
                                                                (Efield
                                                                  (Ederef
                                                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                  _receiving_counter
                                                                  (Tstruct _noise_replay_counter noattr))
                                                                _backtrack
                                                                (tarray tulong 128))
                                                              (Etempvar _j tulong)
                                                              (tptr tulong))
                                                            tulong)
                                                          (Ecast
                                                            (Etempvar _t'13 tulong)
                                                            tulong))))
                                                    (Sset _j
                                                      (Ebinop Oadd
                                                        (Etempvar _j tulong)
                                                        (Econst_int (Int.repr 1) tint)
                                                        tulong))))
                                                (Ssequence
                                                  (Ssequence
                                                    (Scall (Some _t'14)
                                                      (Evar _nondet_u32 
                                                      (Tfunction nil tuint
                                                        cc_default)) nil)
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                          (Tstruct _noise_keypair noattr))
                                                        _remote_index tuint)
                                                      (Etempvar _t'14 tuint)))
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'15)
                                                        (Evar _nondet_u8 
                                                        (Tfunction nil tuchar
                                                          cc_default)) nil)
                                                      (Sassign
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                            (Tstruct _noise_keypair noattr))
                                                          _i_am_the_initiator
                                                          tbool)
                                                        (Ebinop Oand
                                                          (Etempvar _t'15 tuchar)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tint)))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'16)
                                                          (Evar _draw_peer_refs 
                                                          (Tfunction nil
                                                            tuint cc_default))
                                                          nil)
                                                        (Sassign
                                                          (Efield
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                                (Tstruct _noise_keypair noattr))
                                                              _refcount
                                                              (Tstruct _kref noattr))
                                                            _refcount tuint)
                                                          (Etempvar _t'16 tuint)))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'17)
                                                            (Evar _draw_u64 
                                                            (Tfunction nil
                                                              tulong
                                                              cc_default))
                                                            nil)
                                                          (Sassign
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                                (Tstruct _noise_keypair noattr))
                                                              _internal_id
                                                              tulong)
                                                            (Etempvar _t'17 tulong)))
                                                        (Ssequence
                                                          (Sifthenelse (Etempvar _fill tint)
                                                            (Ssequence
                                                              (Scall (Some _t'18)
                                                                (Evar _nondet_u8 
                                                                (Tfunction
                                                                  nil tuchar
                                                                  cc_default))
                                                                nil)
                                                              (Sswitch 
                                                                (Ebinop Omod
                                                                  (Etempvar _t'18 tuchar)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tint)
                                                                (LScons (Some 0)
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'21
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'21 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                  (LScons (Some 1)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'20
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _previous_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'20 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _previous_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (LScons (Some 2)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'19
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'19 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _owner (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr))))
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (LScons None
                                                                    Sbreak
                                                                    LSnil))))))
                                                            Sskip)
                                                          (Ssequence
                                                            (Sassign
                                                              (Efield
                                                                (Ederef
                                                                  (Etempvar _k (tptr (Tstruct _kent noattr)))
                                                                  (Tstruct _kent noattr))
                                                                _next
                                                                (tptr (Tstruct _kent noattr)))
                                                              (Etempvar _l (tptr (Tstruct _kent noattr))))
                                                            (Sset _l
                                                              (Etempvar _k (tptr (Tstruct _kent noattr)))))))))))))))))))))))))))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Sreturn (Some (Etempvar _l (tptr (Tstruct _kent noattr))))))))
|}.

Definition f_kents_snap := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_j, tulong) ::
               (_kp, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'16, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'15, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'14, tint) :: (_t'13, tuint) :: (_t'12, tbool) ::
               (_t'11, tulong) :: (_t'10, tulong) :: (_t'9, tbool) ::
               (_t'8, tbool) :: (_t'7, tlong) :: (_t'6, tulong) ::
               (_t'5, tulong) :: (_t'4, tuint) :: (_t'3, tbool) ::
               (_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Sloop
  (Ssequence
    (Sifthenelse (Etempvar _l (tptr (Tstruct _kent noattr))) Sskip Sbreak)
    (Ssequence
      (Sset _kp
        (Eaddrof
          (Efield
            (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
              (Tstruct _kent noattr)) _kp (Tstruct _noise_keypair noattr))
          (tptr (Tstruct _noise_keypair noattr))))
      (Ssequence
        (Ssequence
          (Sset _t'16
            (Efield
              (Efield
                (Ederef (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                  (Tstruct _noise_keypair noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _peer
              (tptr (Tstruct _wg_peer noattr))))
          (Sassign
            (Efield
              (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                (Tstruct _kent noattr)) _peer0
              (tptr (Tstruct _wg_peer noattr)))
            (Etempvar _t'16 (tptr (Tstruct _wg_peer noattr)))))
        (Ssequence
          (Ssequence
            (Sset _t'15
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                    (Tstruct _noise_keypair noattr)) _entry
                  (Tstruct _index_hashtable_entry noattr)) _next
                (tptr (Tstruct _index_hashtable_entry noattr))))
            (Sassign
              (Efield
                (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                  (Tstruct _kent noattr)) _next0
                (tptr (Tstruct _index_hashtable_entry noattr)))
              (Etempvar _t'15 (tptr (Tstruct _index_hashtable_entry noattr)))))
          (Ssequence
            (Ssequence
              (Sset _t'14
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                      (Tstruct _noise_keypair noattr)) _entry
                    (Tstruct _index_hashtable_entry noattr)) _type tint))
              (Sassign
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                    (Tstruct _kent noattr)) _type0 tint)
                (Etempvar _t'14 tint)))
            (Ssequence
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                        (Tstruct _noise_keypair noattr)) _entry
                      (Tstruct _index_hashtable_entry noattr)) _index tuint))
                (Sassign
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                      (Tstruct _kent noattr)) _index0 tuint)
                  (Etempvar _t'13 tuint)))
              (Ssequence
                (Ssequence
                  (Sset _t'12
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                          (Tstruct _noise_keypair noattr)) _entry
                        (Tstruct _index_hashtable_entry noattr)) _hashed
                      tbool))
                  (Sassign
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                        (Tstruct _kent noattr)) _hashed0 tbool)
                    (Etempvar _t'12 tbool)))
                (Ssequence
                  (Scall None
                    (Evar _bytes_copy (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tvoid cc_default))
                    ((Efield
                       (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                         (Tstruct _kent noattr)) _skey0 (tarray tuchar 32)) ::
                     (Efield
                       (Efield
                         (Ederef
                           (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                           (Tstruct _noise_keypair noattr)) _sending
                         (Tstruct _noise_symmetric_key noattr)) _key
                       (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _bytes_copy (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tvoid cc_default))
                      ((Efield
                         (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                           (Tstruct _kent noattr)) _rkey0 (tarray tuchar 32)) ::
                       (Efield
                         (Efield
                           (Ederef
                             (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                             (Tstruct _noise_keypair noattr)) _receiving
                           (Tstruct _noise_symmetric_key noattr)) _key
                         (tarray tuchar 32)) ::
                       (Econst_int (Int.repr 32) tint) :: nil))
                    (Ssequence
                      (Ssequence
                        (Sset _t'11
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                (Tstruct _noise_keypair noattr)) _sending
                              (Tstruct _noise_symmetric_key noattr))
                            _birthdate tulong))
                        (Sassign
                          (Efield
                            (Ederef
                              (Etempvar _l (tptr (Tstruct _kent noattr)))
                              (Tstruct _kent noattr)) _sbirth0 tulong)
                          (Etempvar _t'11 tulong)))
                      (Ssequence
                        (Ssequence
                          (Sset _t'10
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                  (Tstruct _noise_keypair noattr)) _receiving
                                (Tstruct _noise_symmetric_key noattr))
                              _birthdate tulong))
                          (Sassign
                            (Efield
                              (Ederef
                                (Etempvar _l (tptr (Tstruct _kent noattr)))
                                (Tstruct _kent noattr)) _rbirth0 tulong)
                            (Etempvar _t'10 tulong)))
                        (Ssequence
                          (Ssequence
                            (Sset _t'9
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                    (Tstruct _noise_keypair noattr)) _sending
                                  (Tstruct _noise_symmetric_key noattr))
                                _is_valid tbool))
                            (Sassign
                              (Efield
                                (Ederef
                                  (Etempvar _l (tptr (Tstruct _kent noattr)))
                                  (Tstruct _kent noattr)) _svalid0 tbool)
                              (Etempvar _t'9 tbool)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'8
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                      (Tstruct _noise_keypair noattr))
                                    _receiving
                                    (Tstruct _noise_symmetric_key noattr))
                                  _is_valid tbool))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _l (tptr (Tstruct _kent noattr)))
                                    (Tstruct _kent noattr)) _rvalid0 tbool)
                                (Etempvar _t'8 tbool)))
                            (Ssequence
                              (Ssequence
                                (Sset _t'7
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                        (Tstruct _noise_keypair noattr))
                                      _sending_counter
                                      (Tstruct ___gp_atomic64_t noattr))
                                    _counter tlong))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _l (tptr (Tstruct _kent noattr)))
                                      (Tstruct _kent noattr)) _scnt0 tlong)
                                  (Etempvar _t'7 tlong)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                          (Tstruct _noise_keypair noattr))
                                        _receiving_counter
                                        (Tstruct _noise_replay_counter noattr))
                                      _counter tulong))
                                  (Sassign
                                    (Efield
                                      (Ederef
                                        (Etempvar _l (tptr (Tstruct _kent noattr)))
                                        (Tstruct _kent noattr)) _rcnt0
                                      tulong) (Etempvar _t'6 tulong)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _j
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        tulong))
                                    (Sloop
                                      (Ssequence
                                        (Sifthenelse (Ebinop Olt
                                                       (Etempvar _j tulong)
                                                       (Ebinop Odiv
                                                         (Econst_int (Int.repr 8192) tint)
                                                         (Econst_int (Int.repr 64) tint)
                                                         tint) tint)
                                          Sskip
                                          Sbreak)
                                        (Ssequence
                                          (Sset _t'5
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                      (Tstruct _noise_keypair noattr))
                                                    _receiving_counter
                                                    (Tstruct _noise_replay_counter noattr))
                                                  _backtrack
                                                  (tarray tulong 128))
                                                (Etempvar _j tulong)
                                                (tptr tulong)) tulong))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _l (tptr (Tstruct _kent noattr)))
                                                    (Tstruct _kent noattr))
                                                  _bt0 (tarray tulong 128))
                                                (Etempvar _j tulong)
                                                (tptr tulong)) tulong)
                                            (Etempvar _t'5 tulong))))
                                      (Sset _j
                                        (Ebinop Oadd (Etempvar _j tulong)
                                          (Econst_int (Int.repr 1) tint)
                                          tulong))))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'4
                                        (Efield
                                          (Ederef
                                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                            (Tstruct _noise_keypair noattr))
                                          _remote_index tuint))
                                      (Sassign
                                        (Efield
                                          (Ederef
                                            (Etempvar _l (tptr (Tstruct _kent noattr)))
                                            (Tstruct _kent noattr))
                                          _remote_index0 tuint)
                                        (Etempvar _t'4 tuint)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'3
                                          (Efield
                                            (Ederef
                                              (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                              (Tstruct _noise_keypair noattr))
                                            _i_am_the_initiator tbool))
                                        (Sassign
                                          (Efield
                                            (Ederef
                                              (Etempvar _l (tptr (Tstruct _kent noattr)))
                                              (Tstruct _kent noattr))
                                            _initiator0 tbool)
                                          (Etempvar _t'3 tbool)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'2
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                  (Tstruct _noise_keypair noattr))
                                                _refcount
                                                (Tstruct _kref noattr))
                                              _refcount tuint))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _l (tptr (Tstruct _kent noattr)))
                                                (Tstruct _kent noattr))
                                              _refs0 tuint)
                                            (Etempvar _t'2 tuint)))
                                        (Ssequence
                                          (Sset _t'1
                                            (Efield
                                              (Ederef
                                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                (Tstruct _noise_keypair noattr))
                                              _internal_id tulong))
                                          (Sassign
                                            (Efield
                                              (Ederef
                                                (Etempvar _l (tptr (Tstruct _kent noattr)))
                                                (Tstruct _kent noattr)) _id0
                                              tulong) (Etempvar _t'1 tulong))))))))))))))))))))))
  (Sset _l
    (Efield
      (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
        (Tstruct _kent noattr)) _next (tptr (Tstruct _kent noattr)))))
|}.

Definition f_kent_same_but_next := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_kp, (tptr (Tstruct _noise_keypair noattr))) ::
               (_j, tulong) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'47, tint) :: (_t'46, tint) ::
               (_t'45, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'44, (tptr (Tstruct _wg_peer noattr))) :: (_t'43, tuint) ::
               (_t'42, tuint) :: (_t'41, tbool) :: (_t'40, tbool) ::
               (_t'39, tulong) :: (_t'38, tulong) :: (_t'37, tulong) ::
               (_t'36, tulong) :: (_t'35, tbool) :: (_t'34, tbool) ::
               (_t'33, tbool) :: (_t'32, tbool) :: (_t'31, tlong) ::
               (_t'30, tlong) :: (_t'29, tulong) :: (_t'28, tulong) ::
               (_t'27, tuint) :: (_t'26, tuint) :: (_t'25, tbool) ::
               (_t'24, tbool) :: (_t'23, tuint) :: (_t'22, tuint) ::
               (_t'21, tulong) :: (_t'20, tulong) :: (_t'19, tulong) ::
               (_t'18, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _kp
    (Eaddrof
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
          (Tstruct _kent noattr)) _kp (Tstruct _noise_keypair noattr))
      (tptr (Tstruct _noise_keypair noattr))))
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Ssequence
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'44
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                            (Tstruct _noise_keypair noattr))
                                          _entry
                                          (Tstruct _index_hashtable_entry noattr))
                                        _peer
                                        (tptr (Tstruct _wg_peer noattr))))
                                    (Ssequence
                                      (Sset _t'45
                                        (Efield
                                          (Ederef
                                            (Etempvar _l (tptr (Tstruct _kent noattr)))
                                            (Tstruct _kent noattr)) _peer0
                                          (tptr (Tstruct _wg_peer noattr))))
                                      (Sifthenelse (Ebinop One
                                                     (Etempvar _t'44 (tptr (Tstruct _wg_peer noattr)))
                                                     (Etempvar _t'45 (tptr (Tstruct _wg_peer noattr)))
                                                     tint)
                                        (Sset _t'1
                                          (Econst_int (Int.repr 1) tint))
                                        (Ssequence
                                          (Sset _t'46
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                                  (Tstruct _noise_keypair noattr))
                                                _entry
                                                (Tstruct _index_hashtable_entry noattr))
                                              _type tint))
                                          (Ssequence
                                            (Sset _t'47
                                              (Efield
                                                (Ederef
                                                  (Etempvar _l (tptr (Tstruct _kent noattr)))
                                                  (Tstruct _kent noattr))
                                                _type0 tint))
                                            (Sset _t'1
                                              (Ecast
                                                (Ebinop One
                                                  (Etempvar _t'46 tint)
                                                  (Etempvar _t'47 tint) tint)
                                                tbool)))))))
                                  (Sifthenelse (Etempvar _t'1 tint)
                                    (Sset _t'2
                                      (Econst_int (Int.repr 1) tint))
                                    (Ssequence
                                      (Sset _t'42
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                              (Tstruct _noise_keypair noattr))
                                            _entry
                                            (Tstruct _index_hashtable_entry noattr))
                                          _index tuint))
                                      (Ssequence
                                        (Sset _t'43
                                          (Efield
                                            (Ederef
                                              (Etempvar _l (tptr (Tstruct _kent noattr)))
                                              (Tstruct _kent noattr)) _index0
                                            tuint))
                                        (Sset _t'2
                                          (Ecast
                                            (Ebinop One
                                              (Etempvar _t'42 tuint)
                                              (Etempvar _t'43 tuint) tint)
                                            tbool))))))
                                (Sifthenelse (Etempvar _t'2 tint)
                                  (Sset _t'3 (Econst_int (Int.repr 1) tint))
                                  (Ssequence
                                    (Sset _t'40
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                            (Tstruct _noise_keypair noattr))
                                          _entry
                                          (Tstruct _index_hashtable_entry noattr))
                                        _hashed tbool))
                                    (Ssequence
                                      (Sset _t'41
                                        (Efield
                                          (Ederef
                                            (Etempvar _l (tptr (Tstruct _kent noattr)))
                                            (Tstruct _kent noattr)) _hashed0
                                          tbool))
                                      (Sset _t'3
                                        (Ecast
                                          (Ebinop One (Etempvar _t'40 tbool)
                                            (Etempvar _t'41 tbool) tint)
                                          tbool))))))
                              (Sifthenelse (Etempvar _t'3 tint)
                                (Sset _t'4 (Econst_int (Int.repr 1) tint))
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _bytes_eq (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                    ((Efield
                                       (Efield
                                         (Ederef
                                           (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                           (Tstruct _noise_keypair noattr))
                                         _sending
                                         (Tstruct _noise_symmetric_key noattr))
                                       _key (tarray tuchar 32)) ::
                                     (Efield
                                       (Ederef
                                         (Etempvar _l (tptr (Tstruct _kent noattr)))
                                         (Tstruct _kent noattr)) _skey0
                                       (tarray tuchar 32)) ::
                                     (Econst_int (Int.repr 32) tint) :: nil))
                                  (Sset _t'4
                                    (Ecast
                                      (Eunop Onotbool (Etempvar _t'5 tint)
                                        tint) tbool)))))
                            (Sifthenelse (Etempvar _t'4 tint)
                              (Sset _t'6 (Econst_int (Int.repr 1) tint))
                              (Ssequence
                                (Scall (Some _t'7)
                                  (Evar _bytes_eq (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                                  ((Efield
                                     (Efield
                                       (Ederef
                                         (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                         (Tstruct _noise_keypair noattr))
                                       _receiving
                                       (Tstruct _noise_symmetric_key noattr))
                                     _key (tarray tuchar 32)) ::
                                   (Efield
                                     (Ederef
                                       (Etempvar _l (tptr (Tstruct _kent noattr)))
                                       (Tstruct _kent noattr)) _rkey0
                                     (tarray tuchar 32)) ::
                                   (Econst_int (Int.repr 32) tint) :: nil))
                                (Sset _t'6
                                  (Ecast
                                    (Eunop Onotbool (Etempvar _t'7 tint)
                                      tint) tbool)))))
                          (Sifthenelse (Etempvar _t'6 tint)
                            (Sset _t'8 (Econst_int (Int.repr 1) tint))
                            (Ssequence
                              (Sset _t'38
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                      (Tstruct _noise_keypair noattr))
                                    _sending
                                    (Tstruct _noise_symmetric_key noattr))
                                  _birthdate tulong))
                              (Ssequence
                                (Sset _t'39
                                  (Efield
                                    (Ederef
                                      (Etempvar _l (tptr (Tstruct _kent noattr)))
                                      (Tstruct _kent noattr)) _sbirth0
                                    tulong))
                                (Sset _t'8
                                  (Ecast
                                    (Ebinop One (Etempvar _t'38 tulong)
                                      (Etempvar _t'39 tulong) tint) tbool))))))
                        (Sifthenelse (Etempvar _t'8 tint)
                          (Sset _t'9 (Econst_int (Int.repr 1) tint))
                          (Ssequence
                            (Sset _t'36
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                    (Tstruct _noise_keypair noattr))
                                  _receiving
                                  (Tstruct _noise_symmetric_key noattr))
                                _birthdate tulong))
                            (Ssequence
                              (Sset _t'37
                                (Efield
                                  (Ederef
                                    (Etempvar _l (tptr (Tstruct _kent noattr)))
                                    (Tstruct _kent noattr)) _rbirth0 tulong))
                              (Sset _t'9
                                (Ecast
                                  (Ebinop One (Etempvar _t'36 tulong)
                                    (Etempvar _t'37 tulong) tint) tbool))))))
                      (Sifthenelse (Etempvar _t'9 tint)
                        (Sset _t'10 (Econst_int (Int.repr 1) tint))
                        (Ssequence
                          (Sset _t'34
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                  (Tstruct _noise_keypair noattr)) _sending
                                (Tstruct _noise_symmetric_key noattr))
                              _is_valid tbool))
                          (Ssequence
                            (Sset _t'35
                              (Efield
                                (Ederef
                                  (Etempvar _l (tptr (Tstruct _kent noattr)))
                                  (Tstruct _kent noattr)) _svalid0 tbool))
                            (Sset _t'10
                              (Ecast
                                (Ebinop One (Etempvar _t'34 tbool)
                                  (Etempvar _t'35 tbool) tint) tbool))))))
                    (Sifthenelse (Etempvar _t'10 tint)
                      (Sset _t'11 (Econst_int (Int.repr 1) tint))
                      (Ssequence
                        (Sset _t'32
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                                (Tstruct _noise_keypair noattr)) _receiving
                              (Tstruct _noise_symmetric_key noattr))
                            _is_valid tbool))
                        (Ssequence
                          (Sset _t'33
                            (Efield
                              (Ederef
                                (Etempvar _l (tptr (Tstruct _kent noattr)))
                                (Tstruct _kent noattr)) _rvalid0 tbool))
                          (Sset _t'11
                            (Ecast
                              (Ebinop One (Etempvar _t'32 tbool)
                                (Etempvar _t'33 tbool) tint) tbool))))))
                  (Sifthenelse (Etempvar _t'11 tint)
                    (Sset _t'12 (Econst_int (Int.repr 1) tint))
                    (Ssequence
                      (Sset _t'30
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                              (Tstruct _noise_keypair noattr))
                            _sending_counter
                            (Tstruct ___gp_atomic64_t noattr)) _counter
                          tlong))
                      (Ssequence
                        (Sset _t'31
                          (Efield
                            (Ederef
                              (Etempvar _l (tptr (Tstruct _kent noattr)))
                              (Tstruct _kent noattr)) _scnt0 tlong))
                        (Sset _t'12
                          (Ecast
                            (Ebinop One (Etempvar _t'30 tlong)
                              (Etempvar _t'31 tlong) tint) tbool))))))
                (Sifthenelse (Etempvar _t'12 tint)
                  (Sset _t'13 (Econst_int (Int.repr 1) tint))
                  (Ssequence
                    (Sset _t'28
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                            (Tstruct _noise_keypair noattr))
                          _receiving_counter
                          (Tstruct _noise_replay_counter noattr)) _counter
                        tulong))
                    (Ssequence
                      (Sset _t'29
                        (Efield
                          (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                            (Tstruct _kent noattr)) _rcnt0 tulong))
                      (Sset _t'13
                        (Ecast
                          (Ebinop One (Etempvar _t'28 tulong)
                            (Etempvar _t'29 tulong) tint) tbool))))))
              (Sifthenelse (Etempvar _t'13 tint)
                (Sset _t'14 (Econst_int (Int.repr 1) tint))
                (Ssequence
                  (Sset _t'26
                    (Efield
                      (Ederef
                        (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                        (Tstruct _noise_keypair noattr)) _remote_index tuint))
                  (Ssequence
                    (Sset _t'27
                      (Efield
                        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                          (Tstruct _kent noattr)) _remote_index0 tuint))
                    (Sset _t'14
                      (Ecast
                        (Ebinop One (Etempvar _t'26 tuint)
                          (Etempvar _t'27 tuint) tint) tbool))))))
            (Sifthenelse (Etempvar _t'14 tint)
              (Sset _t'15 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sset _t'24
                  (Efield
                    (Ederef
                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                      (Tstruct _noise_keypair noattr)) _i_am_the_initiator
                    tbool))
                (Ssequence
                  (Sset _t'25
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                        (Tstruct _kent noattr)) _initiator0 tbool))
                  (Sset _t'15
                    (Ecast
                      (Ebinop One (Etempvar _t'24 tbool)
                        (Etempvar _t'25 tbool) tint) tbool))))))
          (Sifthenelse (Etempvar _t'15 tint)
            (Sset _t'16 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'22
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                      (Tstruct _noise_keypair noattr)) _refcount
                    (Tstruct _kref noattr)) _refcount tuint))
              (Ssequence
                (Sset _t'23
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                      (Tstruct _kent noattr)) _refs0 tuint))
                (Sset _t'16
                  (Ecast
                    (Ebinop One (Etempvar _t'22 tuint) (Etempvar _t'23 tuint)
                      tint) tbool))))))
        (Sifthenelse (Etempvar _t'16 tint)
          (Sset _t'17 (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sset _t'20
              (Efield
                (Ederef (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                  (Tstruct _noise_keypair noattr)) _internal_id tulong))
            (Ssequence
              (Sset _t'21
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                    (Tstruct _kent noattr)) _id0 tulong))
              (Sset _t'17
                (Ecast
                  (Ebinop One (Etempvar _t'20 tulong) (Etempvar _t'21 tulong)
                    tint) tbool))))))
      (Sifthenelse (Etempvar _t'17 tint)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        Sskip))
    (Ssequence
      (Ssequence
        (Sset _j (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _j tulong)
                           (Ebinop Odiv (Econst_int (Int.repr 8192) tint)
                             (Econst_int (Int.repr 64) tint) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'18
                (Ederef
                  (Ebinop Oadd
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _kp (tptr (Tstruct _noise_keypair noattr)))
                          (Tstruct _noise_keypair noattr)) _receiving_counter
                        (Tstruct _noise_replay_counter noattr)) _backtrack
                      (tarray tulong 128)) (Etempvar _j tulong)
                    (tptr tulong)) tulong))
              (Ssequence
                (Sset _t'19
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                          (Tstruct _kent noattr)) _bt0 (tarray tulong 128))
                      (Etempvar _j tulong) (tptr tulong)) tulong))
                (Sifthenelse (Ebinop One (Etempvar _t'18 tulong)
                               (Etempvar _t'19 tulong) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))))
          (Sset _j
            (Ebinop Oadd (Etempvar _j tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition f_kents_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) ::
               (_t'4, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'3, (tptr (Tstruct _index_hashtable_entry noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sloop
    (Ssequence
      (Sifthenelse (Etempvar _l (tptr (Tstruct _kent noattr))) Sskip Sbreak)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _kent_same_but_next (Tfunction
                                        ((tptr (Tstruct _kent noattr)) ::
                                         nil) tint cc_default))
            ((Etempvar _l (tptr (Tstruct _kent noattr))) :: nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
            (Sset _t'2 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Sset _t'3
                (Efield
                  (Efield
                    (Efield
                      (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                        (Tstruct _kent noattr)) _kp
                      (Tstruct _noise_keypair noattr)) _entry
                    (Tstruct _index_hashtable_entry noattr)) _next
                  (tptr (Tstruct _index_hashtable_entry noattr))))
              (Ssequence
                (Sset _t'4
                  (Efield
                    (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                      (Tstruct _kent noattr)) _next0
                    (tptr (Tstruct _index_hashtable_entry noattr))))
                (Sset _t'2
                  (Ecast
                    (Ebinop One
                      (Etempvar _t'3 (tptr (Tstruct _index_hashtable_entry noattr)))
                      (Etempvar _t'4 (tptr (Tstruct _index_hashtable_entry noattr)))
                      tint) tbool))))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)))
    (Sset _l
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
          (Tstruct _kent noattr)) _next (tptr (Tstruct _kent noattr)))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_kents_free := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, (tptr (Tstruct _kent noattr))) :: nil);
  fn_body :=
(Swhile
  (Etempvar _l (tptr (Tstruct _kent noattr)))
  (Ssequence
    (Sset _n
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
          (Tstruct _kent noattr)) _next (tptr (Tstruct _kent noattr))))
    (Ssequence
      (Scall None
        (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                                 cc_default))
        ((Etempvar _l (tptr (Tstruct _kent noattr))) :: nil))
      (Sset _l (Etempvar _n (tptr (Tstruct _kent noattr)))))))
|}.

Definition f_skb_take := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _skb_snap noattr))) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr tuchar)) :: (_t'2, tuint) :: (_t'1, tushort) ::
               nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
          (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
    (Sassign
      (Efield
        (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
          (Tstruct _skb_snap noattr)) _data (tptr tuchar))
      (Etempvar _t'3 (tptr tuchar))))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
            (Tstruct _sk_buff noattr)) _len tuint))
      (Sassign
        (Efield
          (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
            (Tstruct _skb_snap noattr)) _len tuint) (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
              (Tstruct _sk_buff noattr)) _protocol tushort))
        (Sassign
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
              (Tstruct _skb_snap noattr)) _protocol tushort)
          (Etempvar _t'1 tushort)))
      (Ssequence
        (Scall None
          (Evar _bytes_copy (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
               (Tstruct _skb_snap noattr)) _saddr4 (tarray tuchar 4)) ::
           (Efield
             (Efield
               (Efield
                 (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                   (Tstruct _sk_buff noattr)) _ip4 (Tstruct _iphdr noattr))
               _saddr (Tstruct _in_addr noattr)) _s_addr (tarray tuchar 4)) ::
           (Econst_int (Int.repr 4) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                 (Tstruct _skb_snap noattr)) _saddr6 (tarray tuchar 16)) ::
             (Efield
               (Efield
                 (Efield
                   (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                     (Tstruct _sk_buff noattr)) _ip6
                   (Tstruct _ipv6hdr noattr)) _saddr
                 (Tstruct _in6_addr noattr)) _s6_addr (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) :: nil))
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                 (Tstruct _skb_snap noattr)) _sport (tarray tuchar 2)) ::
             (Efield
               (Efield
                 (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                   (Tstruct _sk_buff noattr)) _udp (Tstruct _udphdr noattr))
               _source (tarray tuchar 2)) ::
             (Econst_int (Int.repr 2) tint) :: nil)))))))
|}.

Definition f_skb_same := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _skb_snap noattr))) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'14, tuint) ::
               (_t'13, tuint) :: (_t'12, (tptr tuchar)) ::
               (_t'11, (tptr tuchar)) :: (_t'10, tushort) ::
               (_t'9, tushort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'11
              (Efield
                (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                  (Tstruct _skb_snap noattr)) _data (tptr tuchar)))
            (Ssequence
              (Sset _t'12
                (Efield
                  (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                    (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'11 (tptr tuchar))
                             (Etempvar _t'12 (tptr tuchar)) tint)
                (Ssequence
                  (Sset _t'13
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                        (Tstruct _skb_snap noattr)) _len tuint))
                  (Ssequence
                    (Sset _t'14
                      (Efield
                        (Ederef
                          (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                          (Tstruct _sk_buff noattr)) _len tuint))
                    (Sset _t'1
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'13 tuint)
                          (Etempvar _t'14 tuint) tint) tbool))))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))))
          (Sifthenelse (Etempvar _t'1 tint)
            (Ssequence
              (Sset _t'9
                (Efield
                  (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                    (Tstruct _skb_snap noattr)) _protocol tushort))
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                      (Tstruct _sk_buff noattr)) _protocol tushort))
                (Sset _t'2
                  (Ecast
                    (Ebinop Oeq (Etempvar _t'9 tushort)
                      (Etempvar _t'10 tushort) tint) tbool))))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Ssequence
            (Scall (Some _t'4)
              (Evar _bytes_eq (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tint cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                   (Tstruct _skb_snap noattr)) _saddr4 (tarray tuchar 4)) ::
               (Efield
                 (Efield
                   (Efield
                     (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                       (Tstruct _sk_buff noattr)) _ip4
                     (Tstruct _iphdr noattr)) _saddr
                   (Tstruct _in_addr noattr)) _s_addr (tarray tuchar 4)) ::
               (Econst_int (Int.repr 4) tint) :: nil))
            (Sset _t'3 (Ecast (Etempvar _t'4 tint) tbool)))
          (Sset _t'3 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'3 tint)
        (Ssequence
          (Scall (Some _t'6)
            (Evar _bytes_eq (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tint cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
                 (Tstruct _skb_snap noattr)) _saddr6 (tarray tuchar 16)) ::
             (Efield
               (Efield
                 (Efield
                   (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                     (Tstruct _sk_buff noattr)) _ip6
                   (Tstruct _ipv6hdr noattr)) _saddr
                 (Tstruct _in6_addr noattr)) _s6_addr (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) :: nil))
          (Sset _t'5 (Ecast (Etempvar _t'6 tint) tbool)))
        (Sset _t'5 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'5 tint)
      (Ssequence
        (Scall (Some _t'8)
          (Evar _bytes_eq (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tint cc_default))
          ((Efield
             (Ederef (Etempvar _s (tptr (Tstruct _skb_snap noattr)))
               (Tstruct _skb_snap noattr)) _sport (tarray tuchar 2)) ::
           (Efield
             (Efield
               (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                 (Tstruct _sk_buff noattr)) _udp (Tstruct _udphdr noattr))
             _source (tarray tuchar 2)) :: (Econst_int (Int.repr 2) tint) ::
           nil))
        (Sset _t'7 (Ecast (Etempvar _t'8 tint) tbool)))
      (Sset _t'7 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'7 tint))))
|}.

Definition f_m_expired := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_birthdate, tulong) :: (_seconds, tulong) ::
                (_now, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Ole
                 (Ecast
                   (Ebinop Oadd (Etempvar _birthdate tulong)
                     (Ebinop Omul (Etempvar _seconds tulong)
                       (Econst_long (Int64.repr 1000000000) tulong) tulong)
                     tulong) tlong) (Ecast (Etempvar _now tulong) tlong)
                 tint)))
|}.

Definition f_m_cookie := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_secret, (tptr tuchar)) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) :: nil);
  fn_vars := ((_buf, (tarray tuchar 18)) :: nil);
  fn_temps := ((_n, tulong) :: (_t'2, tushort) :: (_t'1, tushort) ::
               (_t'4, tushort) :: (_t'3, tushort) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2)
        (Evar _quickproof_swab16 (Tfunction (tushort :: nil) tushort
                                   cc_default))
        ((Ecast (Econst_int (Int.repr 2048) tint) tushort) :: nil))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
              (Tstruct _sk_buff noattr)) _protocol tushort))
        (Sifthenelse (Ebinop Oeq (Etempvar _t'3 tushort)
                       (Etempvar _t'2 tushort) tint)
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Evar _buf (tarray tuchar 18)) ::
               (Efield
                 (Efield
                   (Efield
                     (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                       (Tstruct _sk_buff noattr)) _ip4
                     (Tstruct _iphdr noattr)) _saddr
                   (Tstruct _in_addr noattr)) _s_addr (tarray tuchar 4)) ::
               (Econst_int (Int.repr 4) tint) :: nil))
            (Sset _n (Ecast (Econst_int (Int.repr 4) tint) tulong)))
          (Ssequence
            (Scall (Some _t'1)
              (Evar _quickproof_swab16 (Tfunction (tushort :: nil) tushort
                                         cc_default))
              ((Ecast (Econst_int (Int.repr 34525) tint) tushort) :: nil))
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                    (Tstruct _sk_buff noattr)) _protocol tushort))
              (Sifthenelse (Ebinop Oeq (Etempvar _t'4 tushort)
                             (Etempvar _t'1 tushort) tint)
                (Ssequence
                  (Scall None
                    (Evar _bytes_copy (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tvoid cc_default))
                    ((Evar _buf (tarray tuchar 18)) ::
                     (Efield
                       (Efield
                         (Efield
                           (Ederef
                             (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                             (Tstruct _sk_buff noattr)) _ip6
                           (Tstruct _ipv6hdr noattr)) _saddr
                         (Tstruct _in6_addr noattr)) _s6_addr
                       (tarray tuchar 16)) ::
                     (Econst_int (Int.repr 16) tint) :: nil))
                  (Sset _n (Ecast (Econst_int (Int.repr 16) tint) tulong)))
                Sskip))))))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Ebinop Oadd (Evar _buf (tarray tuchar 18)) (Etempvar _n tulong)
           (tptr tuchar)) ::
         (Efield
           (Efield
             (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
               (Tstruct _sk_buff noattr)) _udp (Tstruct _udphdr noattr))
           _source (tarray tuchar 2)) :: (Econst_int (Int.repr 2) tint) ::
         nil))
      (Scall None
        (Evar _m_mac (Tfunction
                       ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                        (tptr tuchar) :: tulong :: nil) tvoid cc_default))
        ((Etempvar _out (tptr tuchar)) :: (Etempvar _secret (tptr tuchar)) ::
         (Econst_int (Int.repr 32) tint) :: (Evar _buf (tarray tuchar 18)) ::
         (Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 2) tint)
           tulong) :: nil)))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_wa, (Tstruct _wg_device noattr)) ::
              (_wb, (Tstruct _wg_device noattr)) ::
              (_ita, (Tstruct _index_hashtable noattr)) ::
              (_itb, (Tstruct _index_hashtable noattr)) ::
              (_pta, (Tstruct _pubkey_hashtable noattr)) ::
              (_ptb, (Tstruct _pubkey_hashtable noattr)) ::
              (_ib, (Tstruct _m_identity noattr)) ::
              (_skb, (Tstruct _sk_buff noattr)) ::
              (_raw_a, (tarray tuchar 32)) :: (_raw_b, (tarray tuchar 32)) ::
              (_pub, (tarray tuchar 32)) :: (_secret, (tarray tuchar 32)) ::
              (_cookie__1, (tarray tuchar 16)) :: (_k, (tarray tuchar 32)) ::
              (_enc, (tarray tuchar 32)) :: (_img, (tarray tuchar 64)) ::
              (_img2, (tarray tuchar 64)) ::
              (_peers, (tptr (Tstruct _hnode noattr))) ::
              (_da, (Tstruct _dev_snap noattr)) ::
              (_db, (Tstruct _dev_snap noattr)) ::
              (_sks, (Tstruct _skb_snap noattr)) ::
              (_ss, (Tstruct _shim_snap noattr)) ::
              (_pt, (tarray tuchar 16)) :: nil);
  fn_temps := ((_msg, (tptr tuchar)) :: (_copy, (tptr tuchar)) ::
               (_len, tulong) :: (_n, tulong) :: (_i, tulong) ::
               (_now, tulong) :: (_secret_birth, tulong) ::
               (_index, tuint) ::
               (_reply, (tptr (Tstruct _message_handshake_cookie noattr))) ::
               (_np, (tptr (Tstruct _hnode noattr))) ::
               (_it, (tptr (Tstruct _hnode noattr))) ::
               (_kes, (tptr (Tstruct _kent noattr))) ::
               (_cns, (tptr (Tstruct _cnode noattr))) ::
               (_cn, (tptr (Tstruct _cnode noattr))) ::
               (_target, (tptr (Tstruct _cnode noattr))) ::
               (_head0, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_e, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_mode, tint) :: (_honest, tint) :: (_edge, tulong) ::
               (_h, (tptr (Tstruct _noise_handshake noattr))) ::
               (_kk, tulong) :: (_d, tuchar) :: (_kk__1, tulong) ::
               (_c, (tptr (Tstruct _cookie noattr))) ::
               (_tn, (tptr (Tstruct _hnode noattr))) :: (_t'78, tint) ::
               (_t'77, tint) :: (_t'76, tint) :: (_t'75, tint) ::
               (_t'74, tint) :: (_t'73, tint) :: (_t'72, tint) ::
               (_t'71, tint) :: (_t'70, tint) :: (_t'69, tint) ::
               (_t'68, tint) :: (_t'67, tint) :: (_t'66, tint) ::
               (_t'65, tint) :: (_t'64, tint) :: (_t'63, tint) ::
               (_t'62, tint) :: (_t'61, tint) :: (_t'60, tbool) ::
               (_t'59, tint) :: (_t'58, tint) :: (_t'57, tint) ::
               (_t'56, tint) :: (_t'55, tint) :: (_t'54, tint) ::
               (_t'53, tint) :: (_t'52, tint) :: (_t'51, tint) ::
               (_t'50, tint) :: (_t'49, tint) :: (_t'48, tint) ::
               (_t'47, tint) :: (_t'46, tint) :: (_t'45, tulong) ::
               (_t'44, tint) :: (_t'43, tuchar) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tulong) :: (_t'39, tuchar) ::
               (_t'38, tulong) :: (_t'37, tuchar) ::
               (_t'36, (tptr (Tstruct _kent noattr))) ::
               (_t'35, (tptr tvoid)) :: (_t'34, tuchar) :: (_t'33, tulong) ::
               (_t'32, (tptr (Tstruct _hnode noattr))) :: (_t'31, tint) ::
               (_t'30, tint) :: (_t'29, tint) :: (_t'28, tint) ::
               (_t'27, tint) :: (_t'26, tint) :: (_t'25, tint) ::
               (_t'24, tint) :: (_t'23, tint) :: (_t'22, tint) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tuint) ::
               (_t'18, tuchar) :: (_t'17, tuchar) :: (_t'16, tint) ::
               (_t'15, tuchar) :: (_t'14, tulong) :: (_t'13, tuint) ::
               (_t'12, tushort) :: (_t'11, tushort) :: (_t'10, tuchar) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, tint) :: (_t'3, tulong) :: (_t'2, tulong) ::
               (_t'1, tulong) :: (_t'128, tulong) :: (_t'127, tulong) ::
               (_t'126, tint) :: (_t'125, tuint) :: (_t'124, tuint) ::
               (_t'123, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'122, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'121, (tptr (Tstruct _hnode noattr))) ::
               (_t'120, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'119, tbool) :: (_t'118, tuint) ::
               (_t'117, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'116, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'115, tuint) :: (_t'114, tuint) :: (_t'113, tuchar) ::
               (_t'112, tuchar) ::
               (_t'111, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'110, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'109, tuint) :: (_t'108, (tptr (Tstruct _hnode noattr))) ::
               (_t'107, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'106, (tptr (Tstruct _hnode noattr))) :: (_t'105, tuint) ::
               (_t'104, tuint) :: (_t'103, tint) ::
               (_t'102, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'101, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'100, (tptr (Tstruct _hnode noattr))) :: (_t'99, tbool) ::
               (_t'98, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'97, (tptr (Tstruct _hnode noattr))) :: (_t'96, tulong) ::
               (_t'95, tbool) :: (_t'94, tbool) ::
               (_t'93, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'92, (tptr (Tstruct _hnode noattr))) ::
               (_t'91, (tptr (Tstruct _hnode noattr))) ::
               (_t'90, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'89, (tptr (Tstruct _hnode noattr))) ::
               (_t'88, (tptr (Tstruct _wg_peer noattr))) :: (_t'87, tuint) ::
               (_t'86, tuint) :: (_t'85, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'84, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'83, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'82, tint) :: (_t'81, (tptr (Tstruct _hnode noattr))) ::
               (_t'80, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'79, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign (Evar _peers (tptr (Tstruct _hnode noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sset _cns (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _draw_boottime (Tfunction nil tulong cc_default)) nil)
          (Sassign (Evar _wg_shim_boottime_ns tulong) (Etempvar _t'1 tulong)))
        (Ssequence
          (Scall None (Evar _wg_noise_init (Tfunction nil tvoid cc_default))
            nil)
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Evar _raw_a (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _nondet_bytes (Tfunction
                                      ((tptr tuchar) :: tulong :: nil) tvoid
                                      cc_default))
                ((Evar _raw_b (tarray tuchar 32)) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _setup_device (Tfunction
                                        ((tptr (Tstruct _wg_device noattr)) ::
                                         (tptr (Tstruct _index_hashtable noattr)) ::
                                         (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                         (tptr tuchar) :: nil) tvoid
                                        cc_default))
                  ((Eaddrof (Evar _wa (Tstruct _wg_device noattr))
                     (tptr (Tstruct _wg_device noattr))) ::
                   (Eaddrof (Evar _ita (Tstruct _index_hashtable noattr))
                     (tptr (Tstruct _index_hashtable noattr))) ::
                   (Eaddrof (Evar _pta (Tstruct _pubkey_hashtable noattr))
                     (tptr (Tstruct _pubkey_hashtable noattr))) ::
                   (Evar _raw_a (tarray tuchar 32)) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _setup_device (Tfunction
                                          ((tptr (Tstruct _wg_device noattr)) ::
                                           (tptr (Tstruct _index_hashtable noattr)) ::
                                           (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                           (tptr tuchar) :: nil) tvoid
                                          cc_default))
                    ((Eaddrof (Evar _wb (Tstruct _wg_device noattr))
                       (tptr (Tstruct _wg_device noattr))) ::
                     (Eaddrof (Evar _itb (Tstruct _index_hashtable noattr))
                       (tptr (Tstruct _index_hashtable noattr))) ::
                     (Eaddrof (Evar _ptb (Tstruct _pubkey_hashtable noattr))
                       (tptr (Tstruct _pubkey_hashtable noattr))) ::
                     (Evar _raw_b (tarray tuchar 32)) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _m_identity_of (Tfunction
                                             ((tptr (Tstruct _m_identity noattr)) ::
                                              (tptr tuchar) :: nil) tvoid
                                             cc_default))
                      ((Eaddrof (Evar _ib (Tstruct _m_identity noattr))
                         (tptr (Tstruct _m_identity noattr))) ::
                       (Evar _raw_b (tarray tuchar 32)) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Efield
                           (Efield (Evar _wb (Tstruct _wg_device noattr))
                             _cookie_checker
                             (Tstruct _cookie_checker noattr)) _secret
                           (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'2)
                            (Evar _draw_boottime (Tfunction nil tulong
                                                   cc_default)) nil)
                          (Sassign
                            (Efield
                              (Efield (Evar _wb (Tstruct _wg_device noattr))
                                _cookie_checker
                                (Tstruct _cookie_checker noattr))
                              _secret_birthdate tulong)
                            (Etempvar _t'2 tulong)))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _draw_size (Tfunction nil tulong
                                                 cc_default)) nil)
                            (Sset _len (Etempvar _t'3 tulong)))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Ebinop Ogt (Etempvar _len tulong)
                                             (Ebinop Osub
                                               (Econst_long (Int64.repr (-1)) tulong)
                                               (Econst_int (Int.repr 32) tint)
                                               tulong) tint)
                                (Sset _t'4 (Econst_int (Int.repr 1) tint))
                                (Sset _t'4
                                  (Ecast
                                    (Ebinop Ogt
                                      (Ebinop Oadd (Etempvar _len tulong)
                                        (Econst_int (Int.repr 32) tint)
                                        tulong)
                                      (Econst_int (Int.repr (-1)) tuint)
                                      tint) tbool)))
                              (Sifthenelse (Etempvar _t'4 tint)
                                (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                Sskip))
                            (Ssequence
                              (Sset _len
                                (Ebinop Oadd (Etempvar _len tulong)
                                  (Econst_int (Int.repr 32) tint) tulong))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'5)
                                    (Evar _quickproof_malloc (Tfunction
                                                               (tulong ::
                                                                nil)
                                                               (tptr tvoid)
                                                               cc_default))
                                    ((Etempvar _len tulong) :: nil))
                                  (Sset _msg (Etempvar _t'5 (tptr tvoid))))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'6)
                                      (Evar _quickproof_malloc (Tfunction
                                                                 (tulong ::
                                                                  nil)
                                                                 (tptr tvoid)
                                                                 cc_default))
                                      ((Etempvar _len tulong) :: nil))
                                    (Sset _copy (Etempvar _t'6 (tptr tvoid))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'7)
                                        (Evar _quickproof_malloc (Tfunction
                                                                   (tulong ::
                                                                    nil)
                                                                   (tptr tvoid)
                                                                   cc_default))
                                        ((Esizeof (Tstruct _message_handshake_cookie noattr) tulong) ::
                                         nil))
                                      (Sset _reply
                                        (Etempvar _t'7 (tptr tvoid))))
                                    (Ssequence
                                      (Ssequence
                                        (Ssequence
                                          (Sifthenelse (Ebinop Oeq
                                                         (Etempvar _msg (tptr tuchar))
                                                         (Ecast
                                                           (Econst_int (Int.repr 0) tint)
                                                           (tptr tvoid))
                                                         tint)
                                            (Sset _t'8
                                              (Econst_int (Int.repr 1) tint))
                                            (Sset _t'8
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _copy (tptr tuchar))
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    (tptr tvoid)) tint)
                                                tbool)))
                                          (Sifthenelse (Etempvar _t'8 tint)
                                            (Sset _t'9
                                              (Econst_int (Int.repr 1) tint))
                                            (Sset _t'9
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                  (Ecast
                                                    (Econst_int (Int.repr 0) tint)
                                                    (tptr tvoid)) tint)
                                                tbool))))
                                        (Sifthenelse (Etempvar _t'9 tint)
                                          (Ssequence
                                            (Scall None
                                              (Evar _quickproof_free 
                                              (Tfunction
                                                ((tptr tvoid) :: nil) tvoid
                                                cc_default))
                                              ((Etempvar _msg (tptr tuchar)) ::
                                               nil))
                                            (Ssequence
                                              (Scall None
                                                (Evar _quickproof_free 
                                                (Tfunction
                                                  ((tptr tvoid) :: nil) tvoid
                                                  cc_default))
                                                ((Etempvar _copy (tptr tuchar)) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                   nil))
                                                (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                                          Sskip))
                                      (Ssequence
                                        (Scall None
                                          (Evar _nondet_bytes (Tfunction
                                                                ((tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                          ((Etempvar _msg (tptr tuchar)) ::
                                           (Etempvar _len tulong) :: nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _bytes_copy (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tvoid
                                                                cc_default))
                                            ((Etempvar _copy (tptr tuchar)) ::
                                             (Etempvar _msg (tptr tuchar)) ::
                                             (Etempvar _len tulong) :: nil))
                                          (Ssequence
                                            (Sassign
                                              (Efield
                                                (Evar _skb (Tstruct _sk_buff noattr))
                                                _data (tptr tuchar))
                                              (Etempvar _msg (tptr tuchar)))
                                            (Ssequence
                                              (Sassign
                                                (Efield
                                                  (Evar _skb (Tstruct _sk_buff noattr))
                                                  _len tuint)
                                                (Ecast (Etempvar _len tulong)
                                                  tuint))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'10)
                                                    (Evar _nondet_u8 
                                                    (Tfunction nil tuchar
                                                      cc_default)) nil)
                                                  (Sswitch (Ebinop Omod
                                                             (Etempvar _t'10 tuchar)
                                                             (Econst_int (Int.repr 3) tint)
                                                             tint)
                                                    (LScons (Some 0)
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'11)
                                                            (Evar _quickproof_swab16 
                                                            (Tfunction
                                                              (tushort ::
                                                               nil) tushort
                                                              cc_default))
                                                            ((Ecast
                                                               (Econst_int (Int.repr 2048) tint)
                                                               tushort) ::
                                                             nil))
                                                          (Sassign
                                                            (Efield
                                                              (Evar _skb (Tstruct _sk_buff noattr))
                                                              _protocol
                                                              tushort)
                                                            (Etempvar _t'11 tushort)))
                                                        Sbreak)
                                                      (LScons (Some 1)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'12)
                                                              (Evar _quickproof_swab16 
                                                              (Tfunction
                                                                (tushort ::
                                                                 nil) tushort
                                                                cc_default))
                                                              ((Ecast
                                                                 (Econst_int (Int.repr 34525) tint)
                                                                 tushort) ::
                                                               nil))
                                                            (Sassign
                                                              (Efield
                                                                (Evar _skb (Tstruct _sk_buff noattr))
                                                                _protocol
                                                                tushort)
                                                              (Etempvar _t'12 tushort)))
                                                          Sbreak)
                                                        (LScons None
                                                          (Ssequence
                                                            (Ssequence
                                                              (Scall (Some _t'13)
                                                                (Evar _nondet_u32 
                                                                (Tfunction
                                                                  nil tuint
                                                                  cc_default))
                                                                nil)
                                                              (Sassign
                                                                (Efield
                                                                  (Evar _skb (Tstruct _sk_buff noattr))
                                                                  _protocol
                                                                  tushort)
                                                                (Ecast
                                                                  (Etempvar _t'13 tuint)
                                                                  tushort)))
                                                            Sbreak)
                                                          LSnil)))))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _nondet_bytes 
                                                    (Tfunction
                                                      ((tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                                                    ((Efield
                                                       (Efield
                                                         (Efield
                                                           (Evar _skb (Tstruct _sk_buff noattr))
                                                           _ip4
                                                           (Tstruct _iphdr noattr))
                                                         _saddr
                                                         (Tstruct _in_addr noattr))
                                                       _s_addr
                                                       (tarray tuchar 4)) ::
                                                     (Econst_int (Int.repr 4) tint) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _nondet_bytes 
                                                      (Tfunction
                                                        ((tptr tuchar) ::
                                                         tulong :: nil) tvoid
                                                        cc_default))
                                                      ((Efield
                                                         (Efield
                                                           (Efield
                                                             (Evar _skb (Tstruct _sk_buff noattr))
                                                             _ip6
                                                             (Tstruct _ipv6hdr noattr))
                                                           _saddr
                                                           (Tstruct _in6_addr noattr))
                                                         _s6_addr
                                                         (tarray tuchar 16)) ::
                                                       (Econst_int (Int.repr 16) tint) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _nondet_bytes 
                                                        (Tfunction
                                                          ((tptr tuchar) ::
                                                           tulong :: nil)
                                                          tvoid cc_default))
                                                        ((Efield
                                                           (Efield
                                                             (Evar _skb (Tstruct _sk_buff noattr))
                                                             _udp
                                                             (Tstruct _udphdr noattr))
                                                           _source
                                                           (tarray tuchar 2)) ::
                                                         (Econst_int (Int.repr 2) tint) ::
                                                         nil))
                                                      (Ssequence
                                                        (Ssequence
                                                          (Scall (Some _t'14)
                                                            (Evar _draw_boottime 
                                                            (Tfunction nil
                                                              tulong
                                                              cc_default))
                                                            nil)
                                                          (Sset _now
                                                            (Etempvar _t'14 tulong)))
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'18)
                                                              (Evar _nondet_u8 
                                                              (Tfunction nil
                                                                tuchar
                                                                cc_default))
                                                              nil)
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Ebinop Omod
                                                                  (Etempvar _t'18 tuchar)
                                                                  (Econst_int (Int.repr 4) tint)
                                                                  tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'15)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sifthenelse 
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'15 tuchar)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Sset _t'16
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 120) tint)
                                                                    tint))
                                                                    (Sset _t'16
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 115) tint)
                                                                    tint))))
                                                                    (Scall (Some _t'17)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil))
                                                                  (Ssequence
                                                                    (Sset _t'128
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _secret_birthdate
                                                                    tulong))
                                                                    (Sset _edge
                                                                    (Ebinop Oadd
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _t'128 tulong)
                                                                    (Ebinop Omul
                                                                    (Etempvar _t'16 tint)
                                                                    (Econst_long (Int64.repr 1000000000) tulong)
                                                                    tulong)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tulong)
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'17 tuchar)
                                                                    (Econst_int (Int.repr 5) tint)
                                                                    tint)
                                                                    tulong))))
                                                                (Sifthenelse 
                                                                  (Ebinop Olt
                                                                    (Etempvar _edge tulong)
                                                                    (Ebinop Oshl
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    (Econst_int (Int.repr 62) tint)
                                                                    tulong)
                                                                    tint)
                                                                  (Sset _now
                                                                    (Etempvar _edge tulong))
                                                                  Sskip))
                                                              Sskip))
                                                          (Ssequence
                                                            (Sassign
                                                              (Evar _wg_shim_boottime_ns tulong)
                                                              (Etempvar _now tulong))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Scall (Some _t'19)
                                                                  (Evar _nondet_u32 
                                                                  (Tfunction
                                                                    nil tuint
                                                                    cc_default))
                                                                  nil)
                                                                (Sset _index
                                                                  (Etempvar _t'19 tuint)))
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _fill_cookie_msg 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Sset _secret_birth
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _secret_birthdate
                                                                    tulong))
                                                                  (Ssequence
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _secret (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _secret
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _dev_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _dev_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _db (Tstruct _dev_snap noattr))
                                                                    (tptr (Tstruct _dev_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _skb_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _skb_snap noattr)) ::
                                                                    (tptr (Tstruct _sk_buff noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _sks (Tstruct _skb_snap noattr))
                                                                    (tptr (Tstruct _skb_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _skb (Tstruct _sk_buff noattr))
                                                                    (tptr (Tstruct _sk_buff noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _wg_cookie_message_create 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    (tptr (Tstruct _sk_buff noattr)) ::
                                                                    tuint ::
                                                                    (tptr (Tstruct _cookie_checker noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _skb (Tstruct _sk_buff noattr))
                                                                    (tptr (Tstruct _sk_buff noattr))) ::
                                                                    (Etempvar _index tuint) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    (tptr (Tstruct _cookie_checker noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
                                                                    (Evar _m_expired 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _secret_birth tulong) ::
                                                                    (Econst_int (Int.repr 120) tint) ::
                                                                    (Etempvar _now tulong) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'22 tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _secret (tarray tuchar 32)) ::
                                                                    (Evar _wg_shim_random_log (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _secret_birth
                                                                    (Etempvar _now tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'20)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24)) ::
                                                                    (Evar _wg_shim_random_log_prev (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 24) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'20 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'21)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24)) ::
                                                                    (Evar _wg_shim_random_log (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 24) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'21 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'127
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _secret_birthdate
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'127 tulong)
                                                                    (Etempvar _secret_birth tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _secret
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _secret (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _t'24 tint)
                                                                    tbool)))
                                                                    (Sset _t'23
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'23 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_cookie 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr (Tstruct _sk_buff noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _cookie__1 (tarray tuchar 16)) ::
                                                                    (Evar _secret (tarray tuchar 32)) ::
                                                                    (Eaddrof
                                                                    (Evar _skb (Tstruct _sk_buff noattr))
                                                                    (tptr (Tstruct _sk_buff noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'126
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'126 tint)
                                                                    (Scall None
                                                                    (Evar _m_label_key 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _k (tarray tuchar 32)) ::
                                                                    (Evar _x_cookie_reply__M_LABEL_COOKIE (tarray tuchar 8)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _static_identity
                                                                    (Tstruct _noise_static_identity noattr))
                                                                    _static_public
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _bytes_set 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuchar ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _k (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'25)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _cookie_checker
                                                                    (Tstruct _cookie_checker noattr))
                                                                    _cookie_encryption_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _k (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'25 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'124
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _header
                                                                    (Tstruct _message_header noattr))
                                                                    _type
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'124 tuint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'125
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint))
                                                                    (Sset _t'26
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'125 tuint)
                                                                    (Etempvar _index tuint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'26
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'26 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _xchacha20poly1305_encrypt 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _enc (tarray tuchar 32)) ::
                                                                    (Evar _cookie__1 (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _msg (tptr tuchar))
                                                                    (Etempvar _len tulong)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24)) ::
                                                                    (Evar _k (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'27)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _encrypted_cookie
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _enc (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'27 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'28)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _msg (tptr tuchar)) ::
                                                                    (Etempvar _copy (tptr tuchar)) ::
                                                                    (Etempvar _len tulong) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'28 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _db (Tstruct _dev_snap noattr))
                                                                    _secret
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _secret (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Evar _db (Tstruct _dev_snap noattr))
                                                                    _secret_birthdate
                                                                    tulong)
                                                                    (Etempvar _secret_birth tulong))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'29)
                                                                    (Evar _dev_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _dev_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _db (Tstruct _dev_snap noattr))
                                                                    (tptr (Tstruct _dev_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'29 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'31)
                                                                    (Evar _skb_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _skb_snap noattr)) ::
                                                                    (tptr (Tstruct _sk_buff noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _sks (Tstruct _skb_snap noattr))
                                                                    (tptr (Tstruct _skb_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _skb (Tstruct _sk_buff noattr))
                                                                    (tptr (Tstruct _sk_buff noattr))) ::
                                                                    nil))
                                                                    (Sset _t'30
                                                                    (Ecast
                                                                    (Etempvar _t'31 tint)
                                                                    tbool)))
                                                                    (Sset _t'30
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'30 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'32)
                                                                    (Evar _hnodes_add 
                                                                    (Tfunction
                                                                    ((tptr (tptr (Tstruct _hnode noattr))) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr (Tstruct _hnode noattr))
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr)))
                                                                    (tptr (tptr (Tstruct _hnode noattr)))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    _static_identity
                                                                    (Tstruct _noise_static_identity noattr))
                                                                    _static_public
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    nil))
                                                                    (Sset _np
                                                                    (Etempvar _t'32 (tptr (Tstruct _hnode noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'33)
                                                                    (Evar _draw_steps 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _n
                                                                    (Etempvar _t'33 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tulong))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tulong)
                                                                    (Etempvar _n tulong)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _nondet_bytes 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _pub (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _hnodes_add 
                                                                    (Tfunction
                                                                    ((tptr (tptr (Tstruct _hnode noattr))) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr (Tstruct _hnode noattr))
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr)))
                                                                    (tptr (tptr (Tstruct _hnode noattr)))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    (Evar _pub (tarray tuchar 32)) ::
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Etempvar _i tulong)
                                                                    tulong) ::
                                                                    nil))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _it
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _it (tptr (Tstruct _hnode noattr)))
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'123
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _it (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall None
                                                                    (Evar _peer_randomize_rest 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'123 (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'34)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'34 tuchar)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'122
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _it (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall None
                                                                    (Evar _wg_index_hashtable_insert 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'122 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'35)
                                                                    (Evar _quickproof_malloc 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Esizeof (Tstruct _cnode noattr) tulong) ::
                                                                    nil))
                                                                    (Sset _cn
                                                                    (Etempvar _t'35 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr)))
                                                                    (Etempvar _it (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _cnode noattr)))
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr))))
                                                                    (Sset _cns
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))))))))))
                                                                    (Sset _it
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _it (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _hnode noattr))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'121
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Scall (Some _t'36)
                                                                    (Evar _kents_add 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _hnode noattr)) ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    tint ::
                                                                    nil)
                                                                    (tptr (Tstruct _kent noattr))
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Etempvar _t'121 (tptr (Tstruct _hnode noattr))) ::
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)) ::
                                                                    (Econst_int (Int.repr 1) tint) ::
                                                                    nil)))
                                                                    (Sset _kes
                                                                    (Etempvar _t'36 (tptr (Tstruct _kent noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'37)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _mode
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'37 tuchar)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _honest
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _mode tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Sset _t'44
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'44
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'44 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'120
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sset _h
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'120 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'119
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _hashed
                                                                    tbool))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'119 tbool)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _wg_index_hashtable_insert 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil)
                                                                    tuint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'118
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint)
                                                                    (Etempvar _t'118 tuint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'117
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'117 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _have_sent_mac1
                                                                    tbool)
                                                                    (Econst_int (Int.repr 1) tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'116
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'116 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _last_mac1_sent
                                                                    (tarray tuchar 16)) ::
                                                                    (Ebinop Osub
                                                                    (Ebinop Oadd
                                                                    (Etempvar _msg (tptr tuchar))
                                                                    (Etempvar _len tulong)
                                                                    (tptr tuchar))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _honest
                                                                    (Ebinop Oeq
                                                                    (Etempvar _mode tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _mode tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'38)
                                                                    (Evar _nondet_size 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _kk
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'38 tulong)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'39)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _d
                                                                    (Ecast
                                                                    (Ecast
                                                                    (Ebinop Oadd
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'39 tuchar)
                                                                    (Econst_int (Int.repr 255) tint)
                                                                    tint)
                                                                    tint)
                                                                    tuchar)
                                                                    tuchar)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'115
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _header
                                                                    (Tstruct _message_header noattr))
                                                                    _type
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _header
                                                                    (Tstruct _message_header noattr))
                                                                    _type
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'115 tuint)
                                                                    (Etempvar _d tuchar)
                                                                    tuint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'114
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'114 tuint)
                                                                    (Etempvar _d tuchar)
                                                                    tuint)))
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'113
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24))
                                                                    (Ebinop Osub
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24))
                                                                    (Ebinop Osub
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 8) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'113 tuchar)
                                                                    (Etempvar _d tuchar)
                                                                    tint)))
                                                                    (Ssequence
                                                                    (Sset _t'112
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _encrypted_cookie
                                                                    (tarray tuchar 32))
                                                                    (Ebinop Osub
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _encrypted_cookie
                                                                    (tarray tuchar 32))
                                                                    (Ebinop Osub
                                                                    (Etempvar _kk tulong)
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    tulong)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'112 tuchar)
                                                                    (Etempvar _d tuchar)
                                                                    tint))))))))
                                                                    Sskip)))))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _mode tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _fill_cookie_msg 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'111
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'111 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'43)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'43 tuchar)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'42
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'42 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'40)
                                                                    (Evar _nondet_size 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _kk__1
                                                                    (Etempvar _t'40 tulong)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _e
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'110
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _next
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'110 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'41
                                                                    (Ecast
                                                                    (Ebinop Ogt
                                                                    (Etempvar _kk__1 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'41
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'41 tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Sset _kk__1
                                                                    (Ebinop Osub
                                                                    (Etempvar _kk__1 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)))
                                                                    (Sset _e
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _next
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))))
                                                                    (Ssequence
                                                                    (Sset _t'109
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sassign
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint)
                                                                    (Etempvar _t'109 tuint)))))
                                                                    Sskip)))
                                                                    Sskip)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _cookie_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 64)) ::
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'108
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Scall None
                                                                    (Evar _hnodes_snap 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hnode noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'108 (tptr (Tstruct _hnode noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _cn
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'106
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'107
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'106 (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall None
                                                                    (Evar _ck_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ck_snap noattr)) ::
                                                                    (tptr (Tstruct _cookie noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    (tptr (Tstruct _ck_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'107 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    (tptr (Tstruct _cookie noattr))) ::
                                                                    nil)))))
                                                                    (Sset _cn
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _cnode noattr))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _kents_snap 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _kent noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _dev_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _dev_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _da (Tstruct _dev_snap noattr))
                                                                    (tptr (Tstruct _dev_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _head0
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'45)
                                                                    (Evar _draw_boottime 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sset _now
                                                                    (Etempvar _t'45 tulong)))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Evar _wg_shim_boottime_ns tulong)
                                                                    (Etempvar _now tulong))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _shim_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _shim_snap noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ss (Tstruct _shim_snap noattr))
                                                                    (tptr (Tstruct _shim_snap noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _wg_cookie_message_consume 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _target
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _e
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'104
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'105
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _receiver_index
                                                                    tuint))
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _t'104 tuint)
                                                                    (Etempvar _t'105 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'46
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'46 tint)
                                                                    Sskip
                                                                    Sbreak))
                                                                    (Sset _e
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _next
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'103
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _type
                                                                    tint))
                                                                    (Sset _t'48
                                                                    (Ecast
                                                                    (Ebinop Oand
                                                                    (Etempvar _t'103 tint)
                                                                    (Ebinop Oor
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'48
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'48 tint)
                                                                    (Ssequence
                                                                    (Sset _cn
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'100
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'101
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'100 (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'102
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _peer
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'101 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Etempvar _t'102 (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    (Sset _t'47
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'47
                                                                    (Econst_int (Int.repr 0) tint))))))
                                                                    (Sifthenelse (Etempvar _t'47 tint)
                                                                    (Sset _target
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr))))
                                                                    Sskip)))
                                                                    (Sset _cn
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _cnode noattr))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'99
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _have_sent_mac1
                                                                    tbool))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'99 tbool)
                                                                    tint)
                                                                    (Sset _t'59
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Ssequence
                                                                    (Scall (Some _t'60)
                                                                    (Evar _xchacha20poly1305_decrypt 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Evar _pt (tarray tuchar 16)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _encrypted_cookie
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _last_mac1_sent
                                                                    (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr)))
                                                                    (Tstruct _message_handshake_cookie noattr))
                                                                    _nonce
                                                                    (tarray tuchar 24)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _cookie_decryption_key
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _t'59
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'60 tbool)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sifthenelse (Etempvar _t'59 tint)
                                                                    (Sset _target
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'97
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'98
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'97 (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sset _c
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'98 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    (tptr (Tstruct _cookie noattr))))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'49)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _cookie
                                                                    (tarray tuchar 16)) ::
                                                                    (Evar _pt (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'49 tint)
                                                                    (Ssequence
                                                                    (Sset _t'96
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _birthdate
                                                                    tulong))
                                                                    (Sset _t'50
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'96 tulong)
                                                                    (Etempvar _now tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'50
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'50 tint)
                                                                    (Ssequence
                                                                    (Sset _t'95
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _is_valid
                                                                    tbool))
                                                                    (Sset _t'51
                                                                    (Ecast
                                                                    (Etempvar _t'95 tbool)
                                                                    tbool)))
                                                                    (Sset _t'51
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'51 tint)
                                                                    (Ssequence
                                                                    (Sset _t'94
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _have_sent_mac1
                                                                    tbool))
                                                                    (Sset _t'52
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'94 tbool)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'52
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'52 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'54)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _last_mac1_sent
                                                                    (tarray tuchar 16)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _last_mac1_sent
                                                                    (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))
                                                                    (Sset _t'53
                                                                    (Ecast
                                                                    (Etempvar _t'54 tint)
                                                                    tbool)))
                                                                    (Sset _t'53
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'53 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'56)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _cookie_decryption_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _cookie_decryption_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'55
                                                                    (Ecast
                                                                    (Etempvar _t'56 tint)
                                                                    tbool)))
                                                                    (Sset _t'55
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'55 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'58)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _c (tptr (Tstruct _cookie noattr)))
                                                                    (Tstruct _cookie noattr))
                                                                    _message_mac1_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    _message_mac1_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'57
                                                                    (Ecast
                                                                    (Etempvar _t'58 tint)
                                                                    tbool)))
                                                                    (Sset _t'57
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'57 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _cn
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr))))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    tint)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'92
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'93
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'92 (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall (Some _t'61)
                                                                    (Evar _ck_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _ck_snap noattr)) ::
                                                                    (tptr (Tstruct _cookie noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _cs
                                                                    (Tstruct _ck_snap noattr))
                                                                    (tptr (Tstruct _ck_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'93 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    (tptr (Tstruct _cookie noattr))) ::
                                                                    nil))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'61 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    Sskip))
                                                                    (Sset _cn
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _cnode noattr))))))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'91
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Scall (Some _t'62)
                                                                    (Evar _hnodes_same_except 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hnode noattr)) ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'91 (tptr (Tstruct _hnode noattr))) ::
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid)) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'62 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _tn
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'89
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'90
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall (Some _t'63)
                                                                    (Evar _hnodes_same_except 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hnode noattr)) ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'89 (tptr (Tstruct _hnode noattr))) ::
                                                                    (Etempvar _t'90 (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'63 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'88
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall (Some _t'64)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _snap
                                                                    (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'88 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil)))
                                                                    (Sifthenelse (Etempvar _t'64 tint)
                                                                    (Ssequence
                                                                    (Sset _t'85
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Ssequence
                                                                    (Sset _t'86
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'85 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'87
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _refs
                                                                    tuint))
                                                                    (Sset _t'65
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'86 tuint)
                                                                    (Etempvar _t'87 tuint)
                                                                    tint)
                                                                    tbool)))))
                                                                    (Sset _t'65
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'65 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'84
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall (Some _t'67)
                                                                    (Evar _pr_same_but_cookie 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _pr_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _tn (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _rest
                                                                    (Tstruct _pr_snap noattr))
                                                                    (tptr (Tstruct _pr_snap noattr))) ::
                                                                    (Etempvar _t'84 (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil)))
                                                                    (Sset _t'66
                                                                    (Ecast
                                                                    (Etempvar _t'67 tint)
                                                                    tbool)))
                                                                    (Sset _t'66
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'66 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'68)
                                                                    (Evar _dev_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _dev_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _da (Tstruct _dev_snap noattr))
                                                                    (tptr (Tstruct _dev_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'68 tint)
                                                                    (Ssequence
                                                                    (Sset _t'83
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sset _t'69
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'83 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Etempvar _head0 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'69
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'69 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'71)
                                                                    (Evar _kents_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _kent noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                                    nil))
                                                                    (Sset _t'70
                                                                    (Ecast
                                                                    (Etempvar _t'71 tint)
                                                                    tbool)))
                                                                    (Sset _t'70
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'70 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'73)
                                                                    (Evar _shim_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _shim_snap noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ss (Tstruct _shim_snap noattr))
                                                                    (tptr (Tstruct _shim_snap noattr))) ::
                                                                    nil))
                                                                    (Sset _t'72
                                                                    (Ecast
                                                                    (Etempvar _t'73 tint)
                                                                    tbool)))
                                                                    (Sset _t'72
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'72 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _cookie_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_cookie noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img2 (tarray tuchar 64)) ::
                                                                    (Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'74)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 64)) ::
                                                                    (Evar _img2 (tarray tuchar 64)) ::
                                                                    (Econst_int (Int.repr 64) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'74 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _honest tint)
                                                                    (Sset _t'77
                                                                    (Ecast
                                                                    (Ebinop One
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'77
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'77 tint)
                                                                    (Ssequence
                                                                    (Sset _t'82
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sset _t'78
                                                                    (Ecast
                                                                    (Etempvar _t'82 tint)
                                                                    tbool)))
                                                                    (Sset _t'78
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'78 tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'81
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _target (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _n
                                                                    (tptr (Tstruct _hnode noattr))))
                                                                    (Sset _t'75
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'81 (tptr (Tstruct _hnode noattr)))
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'75
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'75 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'80
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _np (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Scall (Some _t'76)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'80 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _cookie
                                                                    (tarray tuchar 16)) ::
                                                                    (Evar _cookie__1 (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'76 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Swhile
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr)))
                                                                    (Ssequence
                                                                    (Sset _cn
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _cns (tptr (Tstruct _cnode noattr)))
                                                                    (Tstruct _cnode noattr))
                                                                    _next
                                                                    (tptr (Tstruct _cnode noattr))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _cns (tptr (Tstruct _cnode noattr))) ::
                                                                    nil))
                                                                    (Sset _cns
                                                                    (Etempvar _cn (tptr (Tstruct _cnode noattr)))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _kents_free 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _kent noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'79
                                                                    (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                                    (Scall None
                                                                    (Evar _hnodes_free 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hnode noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _t'79 (tptr (Tstruct _hnode noattr))) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _msg (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _copy (tptr tuchar)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _reply (tptr (Tstruct _message_handshake_cookie noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_spinlock_t Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _rw_semaphore Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _rcu_head Struct (Member_plain _unused tint :: nil) noattr ::
 Composite ___gp_atomic64_t Struct
   (Member_plain _counter tlong :: nil)
   noattr ::
 Composite _kref Struct (Member_plain _refcount tuint :: nil) noattr ::
 Composite _blake2s_ctx Struct
   (Member_plain _h (tarray tuint 8) :: Member_plain _t (tarray tuint 2) ::
    Member_plain _f (tarray tuint 2) ::
    Member_plain _buf (tarray tuchar 64) :: Member_plain _buflen tuint ::
    Member_plain _outlen tuint :: nil)
   noattr ::
 Composite _in_addr Struct
   (Member_plain _s_addr (tarray tuchar 4) :: nil)
   noattr ::
 Composite _in6_addr Struct
   (Member_plain _s6_addr (tarray tuchar 16) :: nil)
   noattr ::
 Composite _iphdr Struct
   (Member_plain _saddr (Tstruct _in_addr noattr) :: nil)
   noattr ::
 Composite _ipv6hdr Struct
   (Member_plain _saddr (Tstruct _in6_addr noattr) :: nil)
   noattr ::
 Composite _udphdr Struct
   (Member_plain _source (tarray tuchar 2) :: nil)
   noattr ::
 Composite _net_device Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _sk_buff Struct
   (Member_plain _data (tptr tuchar) :: Member_plain _len tuint ::
    Member_plain _protocol tushort ::
    Member_plain _ip4 (Tstruct _iphdr noattr) ::
    Member_plain _ip6 (Tstruct _ipv6hdr noattr) ::
    Member_plain _udp (Tstruct _udphdr noattr) :: nil)
   noattr ::
 Composite _message_header Struct (Member_plain _type tuint :: nil) noattr ::
 Composite _message_handshake_cookie Struct
   (Member_plain _header (Tstruct _message_header noattr) ::
    Member_plain _receiver_index tuint ::
    Member_plain _nonce (tarray tuchar 24) ::
    Member_plain _encrypted_cookie (tarray tuchar 32) :: nil)
   noattr ::
 Composite _pubkey_hashtable Struct
   (Member_plain _head (tptr (Tstruct _wg_peer noattr)) :: nil)
   noattr ::
 Composite _index_hashtable Struct
   (Member_plain _head (tptr (Tstruct _index_hashtable_entry noattr)) :: nil)
   noattr ::
 Composite _index_hashtable_entry Struct
   (Member_plain _peer (tptr (Tstruct _wg_peer noattr)) ::
    Member_plain _next (tptr (Tstruct _index_hashtable_entry noattr)) ::
    Member_plain _hashed tbool :: Member_plain _type tint ::
    Member_plain _index tuint :: nil)
   noattr ::
 Composite _noise_replay_counter Struct
   (Member_plain _counter tulong ::
    Member_plain _lock (Tstruct ___gp_spinlock_t noattr) ::
    Member_plain _backtrack (tarray tulong 128) :: nil)
   noattr ::
 Composite _noise_symmetric_key Struct
   (Member_plain _key (tarray tuchar 32) :: Member_plain _birthdate tulong ::
    Member_plain _is_valid tbool :: nil)
   noattr ::
 Composite _noise_keypair Struct
   (Member_plain _entry (Tstruct _index_hashtable_entry noattr) ::
    Member_plain _sending (Tstruct _noise_symmetric_key noattr) ::
    Member_plain _sending_counter (Tstruct ___gp_atomic64_t noattr) ::
    Member_plain _receiving (Tstruct _noise_symmetric_key noattr) ::
    Member_plain _receiving_counter (Tstruct _noise_replay_counter noattr) ::
    Member_plain _remote_index tuint ::
    Member_plain _i_am_the_initiator tbool ::
    Member_plain _refcount (Tstruct _kref noattr) ::
    Member_plain _rcu (Tstruct _rcu_head noattr) ::
    Member_plain _internal_id tulong :: nil)
   noattr ::
 Composite _noise_keypairs Struct
   (Member_plain _current_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _previous_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _next_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _keypair_update_lock (Tstruct ___gp_spinlock_t noattr) ::
    nil)
   noattr ::
 Composite _noise_static_identity Struct
   (Member_plain _static_public (tarray tuchar 32) ::
    Member_plain _static_private (tarray tuchar 32) ::
    Member_plain _lock (Tstruct _rw_semaphore noattr) ::
    Member_plain _has_identity tbool :: nil)
   noattr ::
 Composite _noise_handshake Struct
   (Member_plain _entry (Tstruct _index_hashtable_entry noattr) ::
    Member_plain _state tint ::
    Member_plain _last_initiation_consumption tulong ::
    Member_plain _static_identity
      (tptr (Tstruct _noise_static_identity noattr)) ::
    Member_plain _ephemeral_private (tarray tuchar 32) ::
    Member_plain _remote_static (tarray tuchar 32) ::
    Member_plain _remote_ephemeral (tarray tuchar 32) ::
    Member_plain _precomputed_static_static (tarray tuchar 32) ::
    Member_plain _preshared_key (tarray tuchar 32) ::
    Member_plain _hash (tarray tuchar 32) ::
    Member_plain _chaining_key (tarray tuchar 32) ::
    Member_plain _latest_timestamp (tarray tuchar 12) ::
    Member_plain _remote_index tuint ::
    Member_plain _lock (Tstruct _rw_semaphore noattr) :: nil)
   noattr ::
 Composite _cookie_checker Struct
   (Member_plain _secret (tarray tuchar 32) ::
    Member_plain _cookie_encryption_key (tarray tuchar 32) ::
    Member_plain _message_mac1_key (tarray tuchar 32) ::
    Member_plain _secret_birthdate tulong ::
    Member_plain _secret_lock (Tstruct _rw_semaphore noattr) ::
    Member_plain _device (tptr (Tstruct _wg_device noattr)) :: nil)
   noattr ::
 Composite _cookie Struct
   (Member_plain _birthdate tulong :: Member_plain _is_valid tbool ::
    Member_plain _cookie (tarray tuchar 16) ::
    Member_plain _have_sent_mac1 tbool ::
    Member_plain _last_mac1_sent (tarray tuchar 16) ::
    Member_plain _cookie_decryption_key (tarray tuchar 32) ::
    Member_plain _message_mac1_key (tarray tuchar 32) ::
    Member_plain _lock (Tstruct _rw_semaphore noattr) :: nil)
   noattr ::
 Composite _wg_device Struct
   (Member_plain _dev (tptr (Tstruct _net_device noattr)) ::
    Member_plain _static_identity (Tstruct _noise_static_identity noattr) ::
    Member_plain _cookie_checker (Tstruct _cookie_checker noattr) ::
    Member_plain _peer_hashtable (tptr (Tstruct _pubkey_hashtable noattr)) ::
    Member_plain _index_hashtable (tptr (Tstruct _index_hashtable noattr)) ::
    nil)
   noattr ::
 Composite _wg_peer Struct
   (Member_plain _device (tptr (Tstruct _wg_device noattr)) ::
    Member_plain _is_dead tbool ::
    Member_plain _keypairs (Tstruct _noise_keypairs noattr) ::
    Member_plain _handshake (Tstruct _noise_handshake noattr) ::
    Member_plain _last_sent_handshake (Tstruct ___gp_atomic64_t noattr) ::
    Member_plain _latest_cookie (Tstruct _cookie noattr) ::
    Member_plain _refcount (Tstruct _kref noattr) ::
    Member_plain _internal_id tulong ::
    Member_plain _pubkey_next (tptr (Tstruct _wg_peer noattr)) :: nil)
   noattr ::
 Composite _m_identity Struct
   (Member_plain _priv (tarray tuchar 32) ::
    Member_plain _pub (tarray tuchar 32) :: Member_plain _ok tint :: nil)
   noattr ::
 Composite _hs_snap Struct
   (Member_plain _peer (tptr (Tstruct _wg_peer noattr)) ::
    Member_plain _next (tptr (Tstruct _index_hashtable_entry noattr)) ::
    Member_plain _hashed tbool :: Member_plain _type tint ::
    Member_plain _index tuint :: Member_plain _state tint ::
    Member_plain _last_initiation_consumption tulong ::
    Member_plain _static_identity
      (tptr (Tstruct _noise_static_identity noattr)) ::
    Member_plain _ephemeral_private (tarray tuchar 32) ::
    Member_plain _remote_static (tarray tuchar 32) ::
    Member_plain _remote_ephemeral (tarray tuchar 32) ::
    Member_plain _precomputed_static_static (tarray tuchar 32) ::
    Member_plain _preshared_key (tarray tuchar 32) ::
    Member_plain _hash (tarray tuchar 32) ::
    Member_plain _chaining_key (tarray tuchar 32) ::
    Member_plain _latest_timestamp (tarray tuchar 12) ::
    Member_plain _remote_index tuint :: nil)
   noattr ::
 Composite _ck_snap Struct
   (Member_plain _birthdate tulong :: Member_plain _is_valid tbool ::
    Member_plain _cookie (tarray tuchar 16) ::
    Member_plain _have_sent_mac1 tbool ::
    Member_plain _last_mac1_sent (tarray tuchar 16) ::
    Member_plain _cookie_decryption_key (tarray tuchar 32) ::
    Member_plain _message_mac1_key (tarray tuchar 32) :: nil)
   noattr ::
 Composite _pr_snap Struct
   (Member_plain _device (tptr (Tstruct _wg_device noattr)) ::
    Member_plain _is_dead tbool ::
    Member_plain _current_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _previous_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _next_keypair (tptr (Tstruct _noise_keypair noattr)) ::
    Member_plain _last_sent_handshake tlong ::
    Member_plain _cookie (Tstruct _ck_snap noattr) ::
    Member_plain _internal_id tulong ::
    Member_plain _pubkey_next (tptr (Tstruct _wg_peer noattr)) :: nil)
   noattr ::
 Composite _hnode Struct
   (Member_plain _p (tptr (Tstruct _wg_peer noattr)) ::
    Member_plain _snap (Tstruct _hs_snap noattr) ::
    Member_plain _refs tuint ::
    Member_plain _rest (Tstruct _pr_snap noattr) ::
    Member_plain _next (tptr (Tstruct _hnode noattr)) :: nil)
   noattr ::
 Composite _dev_snap Struct
   (Member_plain _dev (tptr (Tstruct _net_device noattr)) ::
    Member_plain _static_public (tarray tuchar 32) ::
    Member_plain _static_private (tarray tuchar 32) ::
    Member_plain _has_identity tbool ::
    Member_plain _secret (tarray tuchar 32) ::
    Member_plain _secret_birthdate tulong ::
    Member_plain _cookie_encryption_key (tarray tuchar 32) ::
    Member_plain _message_mac1_key (tarray tuchar 32) ::
    Member_plain _checker_device (tptr (Tstruct _wg_device noattr)) ::
    Member_plain _peer_hashtable (tptr (Tstruct _pubkey_hashtable noattr)) ::
    Member_plain _index_hashtable (tptr (Tstruct _index_hashtable noattr)) ::
    Member_plain _peers_head (tptr (Tstruct _wg_peer noattr)) :: nil)
   noattr ::
 Composite _shim_snap Struct
   (Member_plain _allocs tulong :: Member_plain _alloc_failures tulong ::
    Member_plain _frees tulong :: Member_plain _peer_released tulong ::
    Member_plain _refcount_warn (tarray tulong 5) :: nil)
   noattr ::
 Composite _kent Struct
   (Member_plain _kp (Tstruct _noise_keypair noattr) ::
    Member_plain _peer0 (tptr (Tstruct _wg_peer noattr)) ::
    Member_plain _next0 (tptr (Tstruct _index_hashtable_entry noattr)) ::
    Member_plain _type0 tint :: Member_plain _index0 tuint ::
    Member_plain _hashed0 tbool :: Member_plain _skey0 (tarray tuchar 32) ::
    Member_plain _rkey0 (tarray tuchar 32) :: Member_plain _sbirth0 tulong ::
    Member_plain _rbirth0 tulong :: Member_plain _svalid0 tbool ::
    Member_plain _rvalid0 tbool :: Member_plain _scnt0 tlong ::
    Member_plain _rcnt0 tulong :: Member_plain _bt0 (tarray tulong 128) ::
    Member_plain _remote_index0 tuint :: Member_plain _initiator0 tbool ::
    Member_plain _refs0 tuint :: Member_plain _id0 tulong ::
    Member_plain _next (tptr (Tstruct _kent noattr)) :: nil)
   noattr ::
 Composite _skb_snap Struct
   (Member_plain _data (tptr tuchar) :: Member_plain _len tuint ::
    Member_plain _protocol tushort ::
    Member_plain _saddr4 (tarray tuchar 4) ::
    Member_plain _saddr6 (tarray tuchar 16) ::
    Member_plain _sport (tarray tuchar 2) :: nil)
   noattr ::
 Composite _cnode Struct
   (Member_plain _n (tptr (Tstruct _hnode noattr)) ::
    Member_plain _cs (Tstruct _ck_snap noattr) ::
    Member_plain _next (tptr (Tstruct _cnode noattr)) :: nil)
   noattr :: nil).

Definition global_definitions : list (ident * globdef fundef type) :=
((___compcert_va_int32,
   Gfun(External (EF_runtime "__compcert_va_int32"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tvoid) :: nil) tuint cc_default)) ::
 (___compcert_va_int64,
   Gfun(External (EF_runtime "__compcert_va_int64"
                   (mksignature (AST.Xptr :: nil) AST.Xlong cc_default))
     ((tptr tvoid) :: nil) tulong cc_default)) ::
 (___compcert_va_float64,
   Gfun(External (EF_runtime "__compcert_va_float64"
                   (mksignature (AST.Xptr :: nil) AST.Xfloat cc_default))
     ((tptr tvoid) :: nil) tdouble cc_default)) ::
 (___compcert_va_composite,
   Gfun(External (EF_runtime "__compcert_va_composite"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) ((tptr tvoid) :: tulong :: nil)
     (tptr tvoid) cc_default)) ::
 (___compcert_i64_dtos,
   Gfun(External (EF_runtime "__compcert_i64_dtos"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tlong cc_default)) ::
 (___compcert_i64_dtou,
   Gfun(External (EF_runtime "__compcert_i64_dtou"
                   (mksignature (AST.Xfloat :: nil) AST.Xlong cc_default))
     (tdouble :: nil) tulong cc_default)) ::
 (___compcert_i64_stod,
   Gfun(External (EF_runtime "__compcert_i64_stod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tlong :: nil) tdouble cc_default)) ::
 (___compcert_i64_utod,
   Gfun(External (EF_runtime "__compcert_i64_utod"
                   (mksignature (AST.Xlong :: nil) AST.Xfloat cc_default))
     (tulong :: nil) tdouble cc_default)) ::
 (___compcert_i64_stof,
   Gfun(External (EF_runtime "__compcert_i64_stof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tlong :: nil) tfloat cc_default)) ::
 (___compcert_i64_utof,
   Gfun(External (EF_runtime "__compcert_i64_utof"
                   (mksignature (AST.Xlong :: nil) AST.Xsingle cc_default))
     (tulong :: nil) tfloat cc_default)) ::
 (___compcert_i64_sdiv,
   Gfun(External (EF_runtime "__compcert_i64_sdiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_udiv,
   Gfun(External (EF_runtime "__compcert_i64_udiv"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_smod,
   Gfun(External (EF_runtime "__compcert_i64_smod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umod,
   Gfun(External (EF_runtime "__compcert_i64_umod"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___compcert_i64_shl,
   Gfun(External (EF_runtime "__compcert_i64_shl"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_shr,
   Gfun(External (EF_runtime "__compcert_i64_shr"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tulong :: tint :: nil) tulong cc_default)) ::
 (___compcert_i64_sar,
   Gfun(External (EF_runtime "__compcert_i64_sar"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xlong
                     cc_default)) (tlong :: tint :: nil) tlong cc_default)) ::
 (___compcert_i64_smulh,
   Gfun(External (EF_runtime "__compcert_i64_smulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___compcert_i64_umulh,
   Gfun(External (EF_runtime "__compcert_i64_umulh"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tulong :: tulong :: nil) tulong
     cc_default)) ::
 (___builtin_ais_annot,
   Gfun(External (EF_builtin "__builtin_ais_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_bswap64,
   Gfun(External (EF_builtin "__builtin_bswap64"
                   (mksignature (AST.Xlong :: nil) AST.Xlong cc_default))
     (tulong :: nil) tulong cc_default)) ::
 (___builtin_bswap,
   Gfun(External (EF_builtin "__builtin_bswap"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap32,
   Gfun(External (EF_builtin "__builtin_bswap32"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tuint cc_default)) ::
 (___builtin_bswap16,
   Gfun(External (EF_builtin "__builtin_bswap16"
                   (mksignature (AST.Xint16unsigned :: nil)
                     AST.Xint16unsigned cc_default)) (tushort :: nil) tushort
     cc_default)) ::
 (___builtin_clz,
   Gfun(External (EF_builtin "__builtin_clz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_clzl,
   Gfun(External (EF_builtin "__builtin_clzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_clzll,
   Gfun(External (EF_builtin "__builtin_clzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctz,
   Gfun(External (EF_builtin "__builtin_ctz"
                   (mksignature (AST.Xint :: nil) AST.Xint cc_default))
     (tuint :: nil) tint cc_default)) ::
 (___builtin_ctzl,
   Gfun(External (EF_builtin "__builtin_ctzl"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_ctzll,
   Gfun(External (EF_builtin "__builtin_ctzll"
                   (mksignature (AST.Xlong :: nil) AST.Xint cc_default))
     (tulong :: nil) tint cc_default)) ::
 (___builtin_fabs,
   Gfun(External (EF_builtin "__builtin_fabs"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fabsf,
   Gfun(External (EF_builtin "__builtin_fabsf"
                   (mksignature (AST.Xsingle :: nil) AST.Xsingle cc_default))
     (tfloat :: nil) tfloat cc_default)) ::
 (___builtin_fsqrt,
   Gfun(External (EF_builtin "__builtin_fsqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_sqrt,
   Gfun(External (EF_builtin "__builtin_sqrt"
                   (mksignature (AST.Xfloat :: nil) AST.Xfloat cc_default))
     (tdouble :: nil) tdouble cc_default)) ::
 (___builtin_memcpy_aligned,
   Gfun(External (EF_builtin "__builtin_memcpy_aligned"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: tulong :: nil) tvoid
     cc_default)) ::
 (___builtin_sel,
   Gfun(External (EF_builtin "__builtin_sel"
                   (mksignature (AST.Xbool :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tbool :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot,
   Gfun(External (EF_builtin "__builtin_annot"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     ((tptr tschar) :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (___builtin_annot_intval,
   Gfun(External (EF_builtin "__builtin_annot_intval"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xint
                     cc_default)) ((tptr tschar) :: tint :: nil) tint
     cc_default)) ::
 (___builtin_membar,
   Gfun(External (EF_builtin "__builtin_membar"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_va_start,
   Gfun(External (EF_builtin "__builtin_va_start"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_va_arg,
   Gfun(External (EF_builtin "__builtin_va_arg"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_va_copy,
   Gfun(External (EF_builtin "__builtin_va_copy"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: (tptr tvoid) :: nil) tvoid
     cc_default)) ::
 (___builtin_va_end,
   Gfun(External (EF_builtin "__builtin_va_end"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (___builtin_unreachable,
   Gfun(External (EF_builtin "__builtin_unreachable"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (___builtin_expect,
   Gfun(External (EF_builtin "__builtin_expect"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xlong
                     cc_default)) (tlong :: tlong :: nil) tlong cc_default)) ::
 (___builtin_fmax,
   Gfun(External (EF_builtin "__builtin_fmax"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmin,
   Gfun(External (EF_builtin "__builtin_fmin"
                   (mksignature (AST.Xfloat :: AST.Xfloat :: nil) AST.Xfloat
                     cc_default)) (tdouble :: tdouble :: nil) tdouble
     cc_default)) ::
 (___builtin_fmadd,
   Gfun(External (EF_builtin "__builtin_fmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fmsub,
   Gfun(External (EF_builtin "__builtin_fmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmadd,
   Gfun(External (EF_builtin "__builtin_fnmadd"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_fnmsub,
   Gfun(External (EF_builtin "__builtin_fnmsub"
                   (mksignature
                     (AST.Xfloat :: AST.Xfloat :: AST.Xfloat :: nil)
                     AST.Xfloat cc_default))
     (tdouble :: tdouble :: tdouble :: nil) tdouble cc_default)) ::
 (___builtin_read16_reversed,
   Gfun(External (EF_builtin "__builtin_read16_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint16unsigned
                     cc_default)) ((tptr tushort) :: nil) tushort
     cc_default)) ::
 (___builtin_read32_reversed,
   Gfun(External (EF_builtin "__builtin_read32_reversed"
                   (mksignature (AST.Xptr :: nil) AST.Xint cc_default))
     ((tptr tuint) :: nil) tuint cc_default)) ::
 (___builtin_write16_reversed,
   Gfun(External (EF_builtin "__builtin_write16_reversed"
                   (mksignature (AST.Xptr :: AST.Xint16unsigned :: nil)
                     AST.Xvoid cc_default))
     ((tptr tushort) :: tushort :: nil) tvoid cc_default)) ::
 (___builtin_write32_reversed,
   Gfun(External (EF_builtin "__builtin_write32_reversed"
                   (mksignature (AST.Xptr :: AST.Xint :: nil) AST.Xvoid
                     cc_default)) ((tptr tuint) :: tuint :: nil) tvoid
     cc_default)) ::
 (___builtin_debug,
   Gfun(External (EF_external "__builtin_debug"
                   (mksignature (AST.Xint :: nil) AST.Xvoid
                     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|}))
     (tint :: nil) tvoid
     {|cc_vararg:=(Some 1); cc_unproto:=false; cc_structret:=false|})) ::
 (_nondet_u8,
   Gfun(External (EF_external "nondet_u8"
                   (mksignature nil AST.Xint8unsigned cc_default)) nil tuchar
     cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_nondet_size,
   Gfun(External (EF_external "nondet_size"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) ::
 (_memcpy,
   Gfun(External (EF_external "memcpy"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_memset,
   Gfun(External (EF_external "memset"
                   (mksignature (AST.Xptr :: AST.Xint :: AST.Xlong :: nil)
                     AST.Xptr cc_default))
     ((tptr tvoid) :: tint :: tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_quickproof_swab16, Gfun(Internal f_quickproof_swab16)) ::
 (_curve25519_generic,
   Gfun(External (EF_external "curve25519_generic"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tvoid
     cc_default)) ::
 (_xchacha20poly1305_encrypt,
   Gfun(External (EF_external "xchacha20poly1305_encrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      (tptr tuchar) :: (tptr tuchar) :: nil) tvoid cc_default)) ::
 (_xchacha20poly1305_decrypt,
   Gfun(External (EF_external "xchacha20poly1305_decrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      (tptr tuchar) :: (tptr tuchar) :: nil) tbool cc_default)) ::
 (___blake2s_init, Gfun(Internal f___blake2s_init)) ::
 (_blake2s_init, Gfun(Internal f_blake2s_init)) ::
 (_blake2s_update,
   Gfun(External (EF_external "blake2s_update"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _blake2s_ctx noattr)) :: (tptr tuchar) :: tulong :: nil)
     tvoid cc_default)) ::
 (_blake2s_final,
   Gfun(External (EF_external "blake2s_final"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _blake2s_ctx noattr)) :: (tptr tuchar) :: nil) tvoid
     cc_default)) :: (_blake2s, Gfun(Internal f_blake2s)) ::
 (_wg_index_hashtable_insert,
   Gfun(External (EF_external "wg_index_hashtable_insert"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) :: nil) tuint
     cc_default)) ::
 (_wg_shim_refcount_warn, Gvar v_wg_shim_refcount_warn) ::
 (_wg_noise_init,
   Gfun(External (EF_external "wg_noise_init"
                   (mksignature nil AST.Xvoid cc_default)) nil tvoid
     cc_default)) ::
 (_wg_noise_handshake_init,
   Gfun(External (EF_external "wg_noise_handshake_init"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xptr :: AST.Xptr ::
                      AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _noise_handshake noattr)) ::
      (tptr (Tstruct _noise_static_identity noattr)) :: (tptr tuchar) ::
      (tptr tuchar) :: (tptr (Tstruct _wg_peer noattr)) :: nil) tvoid
     cc_default)) ::
 (_wg_noise_set_static_identity_private_key,
   Gfun(External (EF_external "wg_noise_set_static_identity_private_key"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _noise_static_identity noattr)) :: (tptr tuchar) :: nil)
     tvoid cc_default)) ::
 (_wg_cookie_checker_init,
   Gfun(External (EF_external "wg_cookie_checker_init"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _cookie_checker noattr)) ::
      (tptr (Tstruct _wg_device noattr)) :: nil) tvoid cc_default)) ::
 (_wg_cookie_checker_precompute_device_keys,
   Gfun(External (EF_external "wg_cookie_checker_precompute_device_keys"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _cookie_checker noattr)) :: nil) tvoid cc_default)) ::
 (_wg_cookie_checker_precompute_peer_keys,
   Gfun(External (EF_external "wg_cookie_checker_precompute_peer_keys"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _wg_peer noattr)) :: nil) tvoid cc_default)) ::
 (_wg_cookie_init,
   Gfun(External (EF_external "wg_cookie_init"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _cookie noattr)) :: nil) tvoid cc_default)) ::
 (_wg_cookie_message_create,
   Gfun(External (EF_external "wg_cookie_message_create"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xint :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr (Tstruct _message_handshake_cookie noattr)) ::
      (tptr (Tstruct _sk_buff noattr)) :: tuint ::
      (tptr (Tstruct _cookie_checker noattr)) :: nil) tvoid cc_default)) ::
 (_wg_cookie_message_consume,
   Gfun(External (EF_external "wg_cookie_message_consume"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _message_handshake_cookie noattr)) ::
      (tptr (Tstruct _wg_device noattr)) :: nil) tvoid cc_default)) ::
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_bytes_set, Gfun(Internal f_bytes_set)) ::
 (_draw_size, Gfun(Internal f_draw_size)) ::
 (_draw_steps, Gfun(Internal f_draw_steps)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_draw_boottime, Gfun(Internal f_draw_boottime)) ::
 (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_random_log, Gvar v_wg_shim_random_log) ::
 (_wg_shim_random_log_prev, Gvar v_wg_shim_random_log_prev) ::
 (_wg_shim_allocs, Gvar v_wg_shim_allocs) ::
 (_wg_shim_alloc_failures, Gvar v_wg_shim_alloc_failures) ::
 (_wg_shim_frees, Gvar v_wg_shim_frees) ::
 (_wg_shim_peer_released, Gvar v_wg_shim_peer_released) ::
 (_le32_store, Gfun(Internal f_le32_store)) ::
 (_m_hash2, Gfun(Internal f_m_hash2)) :: (_m_dh, Gfun(Internal f_m_dh)) ::
 (_x_cookie_reply__M_BASEPOINT, Gvar v_x_cookie_reply__M_BASEPOINT) ::
 (_m_clamp, Gfun(Internal f_m_clamp)) ::
 (_m_identity_of, Gfun(Internal f_m_identity_of)) ::
 (_x_cookie_reply__M_LABEL_COOKIE, Gvar v_x_cookie_reply__M_LABEL_COOKIE) ::
 (_m_label_key, Gfun(Internal f_m_label_key)) ::
 (_m_mac, Gfun(Internal f_m_mac)) ::
 (_setup_device, Gfun(Internal f_setup_device)) ::
 (_setup_peer, Gfun(Internal f_setup_peer)) ::
 (_hs_take, Gfun(Internal f_hs_take)) ::
 (_hs_same, Gfun(Internal f_hs_same)) ::
 (_ck_take, Gfun(Internal f_ck_take)) ::
 (_ck_same, Gfun(Internal f_ck_same)) ::
 (_pr_take, Gfun(Internal f_pr_take)) ::
 (_pr_same_but_cookie, Gfun(Internal f_pr_same_but_cookie)) ::
 (_pr_same, Gfun(Internal f_pr_same)) ::
 (_cookie_img, Gfun(Internal f_cookie_img)) ::
 (_fill_cookie_msg, Gfun(Internal f_fill_cookie_msg)) ::
 (_draw_peer_refs, Gfun(Internal f_draw_peer_refs)) ::
 (_hnodes_snap, Gfun(Internal f_hnodes_snap)) ::
 (_hnodes_same_except, Gfun(Internal f_hnodes_same_except)) ::
 (_hnodes_free, Gfun(Internal f_hnodes_free)) ::
 (_hnodes_add, Gfun(Internal f_hnodes_add)) ::
 (_peer_randomize_rest, Gfun(Internal f_peer_randomize_rest)) ::
 (_hnodes_pick, Gfun(Internal f_hnodes_pick)) ::
 (_dev_take, Gfun(Internal f_dev_take)) ::
 (_dev_same, Gfun(Internal f_dev_same)) ::
 (_shim_take, Gfun(Internal f_shim_take)) ::
 (_shim_no_warning, Gfun(Internal f_shim_no_warning)) ::
 (_shim_same, Gfun(Internal f_shim_same)) ::
 (_kents_add, Gfun(Internal f_kents_add)) ::
 (_kents_snap, Gfun(Internal f_kents_snap)) ::
 (_kent_same_but_next, Gfun(Internal f_kent_same_but_next)) ::
 (_kents_same, Gfun(Internal f_kents_same)) ::
 (_kents_free, Gfun(Internal f_kents_free)) ::
 (_skb_take, Gfun(Internal f_skb_take)) ::
 (_skb_same, Gfun(Internal f_skb_same)) ::
 (_m_expired, Gfun(Internal f_m_expired)) ::
 (_m_cookie, Gfun(Internal f_m_cookie)) :: (_main, Gfun(Internal f_main)) ::
 nil).

Definition public_idents : list ident :=
(_main :: _wg_shim_peer_released :: _wg_shim_frees ::
 _wg_shim_alloc_failures :: _wg_shim_allocs :: _wg_shim_random_log_prev ::
 _wg_shim_random_log :: _wg_shim_boottime_ns :: _wg_cookie_message_consume ::
 _wg_cookie_message_create :: _wg_cookie_init ::
 _wg_cookie_checker_precompute_peer_keys ::
 _wg_cookie_checker_precompute_device_keys :: _wg_cookie_checker_init ::
 _wg_noise_set_static_identity_private_key :: _wg_noise_handshake_init ::
 _wg_noise_init :: _wg_shim_refcount_warn :: _wg_index_hashtable_insert ::
 _blake2s_final :: _blake2s_update :: _xchacha20poly1305_decrypt ::
 _xchacha20poly1305_encrypt :: _curve25519_generic :: _quickproof_free ::
 _quickproof_malloc :: _memset :: _memcpy :: _nondet_bytes :: _nondet_size ::
 _nondet_u32 :: _nondet_u8 :: ___builtin_debug ::
 ___builtin_write32_reversed :: ___builtin_write16_reversed ::
 ___builtin_read32_reversed :: ___builtin_read16_reversed ::
 ___builtin_fnmsub :: ___builtin_fnmadd :: ___builtin_fmsub ::
 ___builtin_fmadd :: ___builtin_fmin :: ___builtin_fmax ::
 ___builtin_expect :: ___builtin_unreachable :: ___builtin_va_end ::
 ___builtin_va_copy :: ___builtin_va_arg :: ___builtin_va_start ::
 ___builtin_membar :: ___builtin_annot_intval :: ___builtin_annot ::
 ___builtin_sel :: ___builtin_memcpy_aligned :: ___builtin_sqrt ::
 ___builtin_fsqrt :: ___builtin_fabsf :: ___builtin_fabs ::
 ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz :: ___builtin_clzll ::
 ___builtin_clzl :: ___builtin_clz :: ___builtin_bswap16 ::
 ___builtin_bswap32 :: ___builtin_bswap :: ___builtin_bswap64 ::
 ___builtin_ais_annot :: ___compcert_i64_umulh :: ___compcert_i64_smulh ::
 ___compcert_i64_sar :: ___compcert_i64_shr :: ___compcert_i64_shl ::
 ___compcert_i64_umod :: ___compcert_i64_smod :: ___compcert_i64_udiv ::
 ___compcert_i64_sdiv :: ___compcert_i64_utof :: ___compcert_i64_stof ::
 ___compcert_i64_utod :: ___compcert_i64_stod :: ___compcert_i64_dtou ::
 ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


