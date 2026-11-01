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
  Definition source_file := "harness/x_handshake.c".
  Definition normalized := true.
End Info.

Definition _x_handshake__M_BASEPOINT : ident := $"x_handshake__M_BASEPOINT".
Definition _x_handshake__M_CONSTRUCTION : ident := $"x_handshake__M_CONSTRUCTION".
Definition _x_handshake__M_IDENTIFIER : ident := $"x_handshake__M_IDENTIFIER".
Definition _x_handshake__M_LABEL_COOKIE : ident := $"x_handshake__M_LABEL_COOKIE".
Definition _x_handshake__M_LABEL_MAC1 : ident := $"x_handshake__M_LABEL_MAC1".
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
Definition _acc1 : ident := $"acc1".
Definition _acc2 : ident := $"acc2".
Definition _agree : ident := $"agree".
Definition _agree__1 : ident := $"agree__1".
Definition _alen : ident := $"alen".
Definition _all_ok : ident := $"all_ok".
Definition _allocs0 : ident := $"allocs0".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _blake2s : ident := $"blake2s".
Definition _blake2s_ctx : ident := $"blake2s_ctx".
Definition _blake2s_final : ident := $"blake2s_final".
Definition _blake2s_init : ident := $"blake2s_init".
Definition _blake2s_update : ident := $"blake2s_update".
Definition _blen : ident := $"blen".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _bytes_copy : ident := $"bytes_copy".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _bytes_set : ident := $"bytes_set".
Definition _bytes_zero : ident := $"bytes_zero".
Definition _c : ident := $"c".
Definition _chacha20poly1305_decrypt : ident := $"chacha20poly1305_decrypt".
Definition _chacha20poly1305_encrypt : ident := $"chacha20poly1305_encrypt".
Definition _chaining_key : ident := $"chaining_key".
Definition _check_failed : ident := $"check_failed".
Definition _ci : ident := $"ci".
Definition _ck : ident := $"ck".
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _counter : ident := $"counter".
Definition _ctx : ident := $"ctx".
Definition _current_keypair : ident := $"current_keypair".
Definition _curve25519_generic : ident := $"curve25519_generic".
Definition _d : ident := $"d".
Definition _d1 : ident := $"d1".
Definition _d1__1 : ident := $"d1__1".
Definition _d2 : ident := $"d2".
Definition _d2__1 : ident := $"d2__1".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _dh : ident := $"dh".
Definition _draw_boottime : ident := $"draw_boottime".
Definition _draw_real_clock : ident := $"draw_real_clock".
Definition _draw_u64 : ident := $"draw_u64".
Definition _e : ident := $"e".
Definition _ei : ident := $"ei".
Definition _enc_nothing : ident := $"enc_nothing".
Definition _enc_static : ident := $"enc_static".
Definition _enc_timestamp : ident := $"enc_timestamp".
Definition _encrypted_nothing : ident := $"encrypted_nothing".
Definition _encrypted_static : ident := $"encrypted_static".
Definition _encrypted_timestamp : ident := $"encrypted_timestamp".
Definition _entry : ident := $"entry".
Definition _eph_priv : ident := $"eph_priv".
Definition _ephemeral : ident := $"ephemeral".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _eraw : ident := $"eraw".
Definition _f : ident := $"f".
Definition _f0 : ident := $"f0".
Definition _fails0 : ident := $"fails0".
Definition _fill_init : ident := $"fill_init".
Definition _fill_resp : ident := $"fill_resp".
Definition _first : ident := $"first".
Definition _frees0 : ident := $"frees0".
Definition _h : ident := $"h".
Definition _h0 : ident := $"h0".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _header : ident := $"header".
Definition _hi : ident := $"hi".
Definition _hs_same : ident := $"hs_same".
Definition _hs_snap : ident := $"hs_snap".
Definition _hs_take : ident := $"hs_take".
Definition _hs_zeroed_from : ident := $"hs_zeroed_from".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _ia : ident := $"ia".
Definition _ib : ident := $"ib".
Definition _id : ident := $"id".
Definition _id_a : ident := $"id_a".
Definition _img : ident := $"img".
Definition _img_before : ident := $"img_before".
Definition _in : ident := $"in".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _init_img : ident := $"init_img".
Definition _inlen : ident := $"inlen".
Definition _inner : ident := $"inner".
Definition _internal_id : ident := $"internal_id".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _it : ident := $"it".
Definition _ita : ident := $"ita".
Definition _itab : ident := $"itab".
Definition _itb : ident := $"itb".
Definition _k : ident := $"k".
Definition _ka : ident := $"ka".
Definition _kb : ident := $"kb".
Definition _key : ident := $"key".
Definition _keylen : ident := $"keylen".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kref : ident := $"kref".
Definition _label : ident := $"label".
Definition _last : ident := $"last".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest : ident := $"latest".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _le32_store : ident := $"le32_store".
Definition _len : ident := $"len".
Definition _lock : ident := $"lock".
Definition _m : ident := $"m".
Definition _m1 : ident := $"m1".
Definition _m2 : ident := $"m2".
Definition _m_clamp : ident := $"m_clamp".
Definition _m_consume_initiation_1 : ident := $"m_consume_initiation_1".
Definition _m_consume_initiation_2 : ident := $"m_consume_initiation_2".
Definition _m_consume_response : ident := $"m_consume_response".
Definition _m_consumed_initiation : ident := $"m_consumed_initiation".
Definition _m_create_initiation : ident := $"m_create_initiation".
Definition _m_create_response : ident := $"m_create_response".
Definition _m_decrypt_and_hash : ident := $"m_decrypt_and_hash".
Definition _m_dh : ident := $"m_dh".
Definition _m_encrypt_and_hash : ident := $"m_encrypt_and_hash".
Definition _m_hash2 : ident := $"m_hash2".
Definition _m_hmac : ident := $"m_hmac".
Definition _m_identity : ident := $"m_identity".
Definition _m_identity_of : ident := $"m_identity_of".
Definition _m_initiation : ident := $"m_initiation".
Definition _m_kdf : ident := $"m_kdf".
Definition _m_label_key : ident := $"m_label_key".
Definition _m_last_consumption : ident := $"m_last_consumption".
Definition _m_mac : ident := $"m_mac".
Definition _m_mix_ck : ident := $"m_mix_ck".
Definition _m_mix_hash : ident := $"m_mix_hash".
Definition _m_mix_key : ident := $"m_mix_key".
Definition _m_mix_psk : ident := $"m_mix_psk".
Definition _m_not_flood : ident := $"m_not_flood".
Definition _m_precomputed : ident := $"m_precomputed".
Definition _m_response : ident := $"m_response".
Definition _m_start : ident := $"m_start".
Definition _m_state : ident := $"m_state".
Definition _m_static_public_field : ident := $"m_static_public_field".
Definition _m_tai64n : ident := $"m_tai64n".
Definition _m_transport : ident := $"m_transport".
Definition _m_ts_newer : ident := $"m_ts_newer".
Definition _mac1 : ident := $"mac1".
Definition _mac2 : ident := $"mac2".
Definition _macs : ident := $"macs".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _message_handshake_initiation : ident := $"message_handshake_initiation".
Definition _message_handshake_response : ident := $"message_handshake_response".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _message_macs : ident := $"message_macs".
Definition _mi : ident := $"mi".
Definition _mok : ident := $"mok".
Definition _mok__1 : ident := $"mok__1".
Definition _mr : ident := $"mr".
Definition _msg : ident := $"msg".
Definition _n : ident := $"n".
Definition _net_device : ident := $"net_device".
Definition _next : ident := $"next".
Definition _next_keypair : ident := $"next_keypair".
Definition _noise_handshake : ident := $"noise_handshake".
Definition _noise_keypair : ident := $"noise_keypair".
Definition _noise_keypairs : ident := $"noise_keypairs".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _noise_static_identity : ident := $"noise_static_identity".
Definition _noise_symmetric_key : ident := $"noise_symmetric_key".
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _nothing : ident := $"nothing".
Definition _now : ident := $"now".
Definition _now_a : ident := $"now_a".
Definition _now_b : ident := $"now_b".
Definition _nsec : ident := $"nsec".
Definition _o : ident := $"o".
Definition _ok : ident := $"ok".
Definition _ok1 : ident := $"ok1".
Definition _ok2 : ident := $"ok2".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _p : ident := $"p".
Definition _pa : ident := $"pa".
Definition _pb : ident := $"pb".
Definition _peer : ident := $"peer".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _peer_pub : ident := $"peer_pub".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _priv : ident := $"priv".
Definition _prk : ident := $"prk".
Definition _psk : ident := $"psk".
Definition _pta : ident := $"pta".
Definition _ptab : ident := $"ptab".
Definition _ptb : ident := $"ptb".
Definition _pub : ident := $"pub".
Definition _pub_ok : ident := $"pub_ok".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _ra : ident := $"ra".
Definition _raw : ident := $"raw".
Definition _raw_a : ident := $"raw_a".
Definition _raw_b : ident := $"raw_b".
Definition _raw_priv : ident := $"raw_priv".
Definition _rb : ident := $"rb".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiver_index : ident := $"receiver_index".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
Definition _resp_img : ident := $"resp_img".
Definition _responder_pub : ident := $"responder_pub".
Definition _ret : ident := $"ret".
Definition _rid : ident := $"rid".
Definition _rimg : ident := $"rimg".
Definition _rimg_before : ident := $"rimg_before".
Definition _rpub : ident := $"rpub".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s : ident := $"s".
Definition _sec : ident := $"sec".
Definition _second : ident := $"second".
Definition _secret : ident := $"secret".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sender_index : ident := $"sender_index".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _setup_device : ident := $"setup_device".
Definition _setup_peer : ident := $"setup_peer".
Definition _si : ident := $"si".
Definition _snap : ident := $"snap".
Definition _spriv : ident := $"spriv".
Definition _spub : ident := $"spub".
Definition _ss : ident := $"ss".
Definition _ssa : ident := $"ssa".
Definition _ssb : ident := $"ssb".
Definition _st : ident := $"st".
Definition _st2 : ident := $"st2".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _t : ident := $"t".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _t3 : ident := $"t3".
Definition _table_has : ident := $"table_has".
Definition _table_index_unique : ident := $"table_index_unique".
Definition _table_len : ident := $"table_len".
Definition _tmp : ident := $"tmp".
Definition _ts : ident := $"ts".
Definition _type : ident := $"type".
Definition _unencrypted_ephemeral : ident := $"unencrypted_ephemeral".
Definition _unused : ident := $"unused".
Definition _use_psk : ident := $"use_psk".
Definition _v : ident := $"v".
Definition _wa : ident := $"wa".
Definition _wb : ident := $"wb".
Definition _wg : ident := $"wg".
Definition _wg_cookie_add_mac_to_packet : ident := $"wg_cookie_add_mac_to_packet".
Definition _wg_cookie_checker_init : ident := $"wg_cookie_checker_init".
Definition _wg_cookie_checker_precompute_device_keys : ident := $"wg_cookie_checker_precompute_device_keys".
Definition _wg_cookie_checker_precompute_peer_keys : ident := $"wg_cookie_checker_precompute_peer_keys".
Definition _wg_cookie_init : ident := $"wg_cookie_init".
Definition _wg_device : ident := $"wg_device".
Definition _wg_noise_handshake_begin_session : ident := $"wg_noise_handshake_begin_session".
Definition _wg_noise_handshake_consume_initiation : ident := $"wg_noise_handshake_consume_initiation".
Definition _wg_noise_handshake_consume_response : ident := $"wg_noise_handshake_consume_response".
Definition _wg_noise_handshake_create_initiation : ident := $"wg_noise_handshake_create_initiation".
Definition _wg_noise_handshake_create_response : ident := $"wg_noise_handshake_create_response".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_init : ident := $"wg_noise_init".
Definition _wg_noise_keypairs_clear : ident := $"wg_noise_keypairs_clear".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_peer_put : ident := $"wg_peer_put".
Definition _wg_shim_alloc_failures : ident := $"wg_shim_alloc_failures".
Definition _wg_shim_allocs : ident := $"wg_shim_allocs".
Definition _wg_shim_boottime_ns : ident := $"wg_shim_boottime_ns".
Definition _wg_shim_frees : ident := $"wg_shim_frees".
Definition _wg_shim_random_log : ident := $"wg_shim_random_log".
Definition _wg_shim_random_u32 : ident := $"wg_shim_random_u32".
Definition _wg_shim_ratelimit_allow : ident := $"wg_shim_ratelimit_allow".
Definition _wg_shim_real_nsec : ident := $"wg_shim_real_nsec".
Definition _wg_shim_real_sec : ident := $"wg_shim_real_sec".
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
Definition _t'129 : ident := 256%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'130 : ident := 257%positive.
Definition _t'131 : ident := 258%positive.
Definition _t'132 : ident := 259%positive.
Definition _t'133 : ident := 260%positive.
Definition _t'134 : ident := 261%positive.
Definition _t'135 : ident := 262%positive.
Definition _t'136 : ident := 263%positive.
Definition _t'137 : ident := 264%positive.
Definition _t'138 : ident := 265%positive.
Definition _t'139 : ident := 266%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'140 : ident := 267%positive.
Definition _t'141 : ident := 268%positive.
Definition _t'142 : ident := 269%positive.
Definition _t'143 : ident := 270%positive.
Definition _t'144 : ident := 271%positive.
Definition _t'145 : ident := 272%positive.
Definition _t'146 : ident := 273%positive.
Definition _t'147 : ident := 274%positive.
Definition _t'148 : ident := 275%positive.
Definition _t'149 : ident := 276%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'150 : ident := 277%positive.
Definition _t'151 : ident := 278%positive.
Definition _t'152 : ident := 279%positive.
Definition _t'153 : ident := 280%positive.
Definition _t'154 : ident := 281%positive.
Definition _t'155 : ident := 282%positive.
Definition _t'156 : ident := 283%positive.
Definition _t'157 : ident := 284%positive.
Definition _t'158 : ident := 285%positive.
Definition _t'159 : ident := 286%positive.
Definition _t'16 : ident := 143%positive.
Definition _t'160 : ident := 287%positive.
Definition _t'161 : ident := 288%positive.
Definition _t'162 : ident := 289%positive.
Definition _t'163 : ident := 290%positive.
Definition _t'164 : ident := 291%positive.
Definition _t'165 : ident := 292%positive.
Definition _t'166 : ident := 293%positive.
Definition _t'167 : ident := 294%positive.
Definition _t'168 : ident := 295%positive.
Definition _t'169 : ident := 296%positive.
Definition _t'17 : ident := 144%positive.
Definition _t'170 : ident := 297%positive.
Definition _t'171 : ident := 298%positive.
Definition _t'172 : ident := 299%positive.
Definition _t'173 : ident := 300%positive.
Definition _t'174 : ident := 301%positive.
Definition _t'175 : ident := 302%positive.
Definition _t'176 : ident := 303%positive.
Definition _t'177 : ident := 304%positive.
Definition _t'178 : ident := 305%positive.
Definition _t'179 : ident := 306%positive.
Definition _t'18 : ident := 145%positive.
Definition _t'180 : ident := 307%positive.
Definition _t'181 : ident := 308%positive.
Definition _t'182 : ident := 309%positive.
Definition _t'183 : ident := 310%positive.
Definition _t'184 : ident := 311%positive.
Definition _t'185 : ident := 312%positive.
Definition _t'186 : ident := 313%positive.
Definition _t'187 : ident := 314%positive.
Definition _t'188 : ident := 315%positive.
Definition _t'189 : ident := 316%positive.
Definition _t'19 : ident := 146%positive.
Definition _t'190 : ident := 317%positive.
Definition _t'191 : ident := 318%positive.
Definition _t'192 : ident := 319%positive.
Definition _t'193 : ident := 320%positive.
Definition _t'194 : ident := 321%positive.
Definition _t'195 : ident := 322%positive.
Definition _t'196 : ident := 323%positive.
Definition _t'197 : ident := 324%positive.
Definition _t'198 : ident := 325%positive.
Definition _t'199 : ident := 326%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'20 : ident := 147%positive.
Definition _t'200 : ident := 327%positive.
Definition _t'201 : ident := 328%positive.
Definition _t'202 : ident := 329%positive.
Definition _t'203 : ident := 330%positive.
Definition _t'204 : ident := 331%positive.
Definition _t'205 : ident := 332%positive.
Definition _t'206 : ident := 333%positive.
Definition _t'207 : ident := 334%positive.
Definition _t'208 : ident := 335%positive.
Definition _t'209 : ident := 336%positive.
Definition _t'21 : ident := 148%positive.
Definition _t'210 : ident := 337%positive.
Definition _t'211 : ident := 338%positive.
Definition _t'212 : ident := 339%positive.
Definition _t'213 : ident := 340%positive.
Definition _t'214 : ident := 341%positive.
Definition _t'215 : ident := 342%positive.
Definition _t'216 : ident := 343%positive.
Definition _t'217 : ident := 344%positive.
Definition _t'218 : ident := 345%positive.
Definition _t'219 : ident := 346%positive.
Definition _t'22 : ident := 149%positive.
Definition _t'220 : ident := 347%positive.
Definition _t'221 : ident := 348%positive.
Definition _t'222 : ident := 349%positive.
Definition _t'223 : ident := 350%positive.
Definition _t'224 : ident := 351%positive.
Definition _t'225 : ident := 352%positive.
Definition _t'226 : ident := 353%positive.
Definition _t'227 : ident := 354%positive.
Definition _t'228 : ident := 355%positive.
Definition _t'229 : ident := 356%positive.
Definition _t'23 : ident := 150%positive.
Definition _t'230 : ident := 357%positive.
Definition _t'231 : ident := 358%positive.
Definition _t'232 : ident := 359%positive.
Definition _t'233 : ident := 360%positive.
Definition _t'234 : ident := 361%positive.
Definition _t'235 : ident := 362%positive.
Definition _t'236 : ident := 363%positive.
Definition _t'237 : ident := 364%positive.
Definition _t'238 : ident := 365%positive.
Definition _t'239 : ident := 366%positive.
Definition _t'24 : ident := 151%positive.
Definition _t'240 : ident := 367%positive.
Definition _t'241 : ident := 368%positive.
Definition _t'242 : ident := 369%positive.
Definition _t'243 : ident := 370%positive.
Definition _t'244 : ident := 371%positive.
Definition _t'245 : ident := 372%positive.
Definition _t'246 : ident := 373%positive.
Definition _t'247 : ident := 374%positive.
Definition _t'248 : ident := 375%positive.
Definition _t'249 : ident := 376%positive.
Definition _t'25 : ident := 152%positive.
Definition _t'250 : ident := 377%positive.
Definition _t'251 : ident := 378%positive.
Definition _t'252 : ident := 379%positive.
Definition _t'253 : ident := 380%positive.
Definition _t'254 : ident := 381%positive.
Definition _t'255 : ident := 382%positive.
Definition _t'256 : ident := 383%positive.
Definition _t'257 : ident := 384%positive.
Definition _t'258 : ident := 385%positive.
Definition _t'259 : ident := 386%positive.
Definition _t'26 : ident := 153%positive.
Definition _t'260 : ident := 387%positive.
Definition _t'261 : ident := 388%positive.
Definition _t'262 : ident := 389%positive.
Definition _t'263 : ident := 390%positive.
Definition _t'264 : ident := 391%positive.
Definition _t'265 : ident := 392%positive.
Definition _t'266 : ident := 393%positive.
Definition _t'267 : ident := 394%positive.
Definition _t'268 : ident := 395%positive.
Definition _t'269 : ident := 396%positive.
Definition _t'27 : ident := 154%positive.
Definition _t'270 : ident := 397%positive.
Definition _t'271 : ident := 398%positive.
Definition _t'272 : ident := 399%positive.
Definition _t'273 : ident := 400%positive.
Definition _t'274 : ident := 401%positive.
Definition _t'275 : ident := 402%positive.
Definition _t'276 : ident := 403%positive.
Definition _t'277 : ident := 404%positive.
Definition _t'278 : ident := 405%positive.
Definition _t'279 : ident := 406%positive.
Definition _t'28 : ident := 155%positive.
Definition _t'280 : ident := 407%positive.
Definition _t'281 : ident := 408%positive.
Definition _t'282 : ident := 409%positive.
Definition _t'283 : ident := 410%positive.
Definition _t'284 : ident := 411%positive.
Definition _t'285 : ident := 412%positive.
Definition _t'286 : ident := 413%positive.
Definition _t'287 : ident := 414%positive.
Definition _t'288 : ident := 415%positive.
Definition _t'289 : ident := 416%positive.
Definition _t'29 : ident := 156%positive.
Definition _t'290 : ident := 417%positive.
Definition _t'291 : ident := 418%positive.
Definition _t'292 : ident := 419%positive.
Definition _t'293 : ident := 420%positive.
Definition _t'294 : ident := 421%positive.
Definition _t'295 : ident := 422%positive.
Definition _t'296 : ident := 423%positive.
Definition _t'297 : ident := 424%positive.
Definition _t'298 : ident := 425%positive.
Definition _t'299 : ident := 426%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'30 : ident := 157%positive.
Definition _t'300 : ident := 427%positive.
Definition _t'301 : ident := 428%positive.
Definition _t'302 : ident := 429%positive.
Definition _t'303 : ident := 430%positive.
Definition _t'304 : ident := 431%positive.
Definition _t'305 : ident := 432%positive.
Definition _t'306 : ident := 433%positive.
Definition _t'307 : ident := 434%positive.
Definition _t'308 : ident := 435%positive.
Definition _t'309 : ident := 436%positive.
Definition _t'31 : ident := 158%positive.
Definition _t'310 : ident := 437%positive.
Definition _t'311 : ident := 438%positive.
Definition _t'312 : ident := 439%positive.
Definition _t'313 : ident := 440%positive.
Definition _t'314 : ident := 441%positive.
Definition _t'315 : ident := 442%positive.
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

Definition v_wg_shim_real_sec := {|
  gvar_info := tlong;
  gvar_init := nil;
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_real_nsec := {|
  gvar_info := tlong;
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

Definition v_wg_shim_random_u32 := {|
  gvar_info := tuint;
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

Definition v_wg_shim_ratelimit_allow := {|
  gvar_info := tbool;
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

Definition f_m_hmac := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_in, (tptr tuchar)) :: (_inlen, tulong) :: nil);
  fn_vars := ((_k, (tarray tuchar 64)) :: (_inner, (tarray tuchar 32)) ::
              nil);
  fn_temps := ((_i, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'4, tuchar) :: (_t'3, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 64) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                         (Econst_int (Int.repr 32) tint) tint)
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Ebinop Oadd (Etempvar _key (tptr tuchar))
                    (Etempvar _i tint) (tptr tuchar)) tuchar))
              (Sset _t'1 (Ecast (Etempvar _t'4 tuchar) tint)))
            (Sset _t'1 (Ecast (Econst_int (Int.repr 0) tint) tint)))
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _k (tarray tuchar 64)) (Etempvar _i tint)
                (tptr tuchar)) tuchar)
            (Ecast
              (Ebinop Oxor (Etempvar _t'1 tint)
                (Econst_int (Int.repr 54) tint) tint) tuchar))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Ssequence
    (Scall None
      (Evar _m_hash2 (Tfunction
                       ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                        (tptr tuchar) :: tulong :: nil) tvoid cc_default))
      ((Evar _inner (tarray tuchar 32)) :: (Evar _k (tarray tuchar 64)) ::
       (Econst_int (Int.repr 64) tint) :: (Etempvar _in (tptr tuchar)) ::
       (Etempvar _inlen tulong) :: nil))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 64) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                             (Econst_int (Int.repr 32) tint) tint)
                (Ssequence
                  (Sset _t'3
                    (Ederef
                      (Ebinop Oadd (Etempvar _key (tptr tuchar))
                        (Etempvar _i tint) (tptr tuchar)) tuchar))
                  (Sset _t'2 (Ecast (Etempvar _t'3 tuchar) tint)))
                (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint)))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _k (tarray tuchar 64))
                    (Etempvar _i tint) (tptr tuchar)) tuchar)
                (Ecast
                  (Ebinop Oxor (Etempvar _t'2 tint)
                    (Econst_int (Int.repr 92) tint) tint) tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Scall None
        (Evar _m_hash2 (Tfunction
                         ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                          (tptr tuchar) :: tulong :: nil) tvoid cc_default))
        ((Etempvar _out (tptr tuchar)) :: (Evar _k (tarray tuchar 64)) ::
         (Econst_int (Int.repr 64) tint) ::
         (Evar _inner (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil)))))
|}.

Definition f_m_kdf := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_t1, (tptr tuchar)) :: (_t2, (tptr tuchar)) ::
                (_t3, (tptr tuchar)) :: (_ck, (tptr tuchar)) ::
                (_in, (tptr tuchar)) :: (_inlen, tulong) :: nil);
  fn_vars := ((_prk, (tarray tuchar 32)) :: (_buf, (tarray tuchar 33)) ::
              nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_hmac (Tfunction
                    ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                     tulong :: nil) tvoid cc_default))
    ((Evar _prk (tarray tuchar 32)) :: (Etempvar _ck (tptr tuchar)) ::
     (Etempvar _in (tptr tuchar)) :: (Etempvar _inlen tulong) :: nil))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _buf (tarray tuchar 33))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Scall None
        (Evar _m_hmac (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                         tulong :: nil) tvoid cc_default))
        ((Etempvar _t1 (tptr tuchar)) :: (Evar _prk (tarray tuchar 32)) ::
         (Evar _buf (tarray tuchar 33)) :: (Econst_int (Int.repr 1) tint) ::
         nil))
      (Ssequence
        (Scall None
          (Evar _bytes_copy (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tvoid cc_default))
          ((Evar _buf (tarray tuchar 33)) :: (Etempvar _t1 (tptr tuchar)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _buf (tarray tuchar 33))
                (Econst_int (Int.repr 32) tint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 2) tint))
          (Ssequence
            (Scall None
              (Evar _m_hmac (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) ::
                               (tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
              ((Etempvar _t2 (tptr tuchar)) ::
               (Evar _prk (tarray tuchar 32)) ::
               (Evar _buf (tarray tuchar 33)) ::
               (Econst_int (Int.repr 33) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _bytes_copy (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tvoid cc_default))
                ((Evar _buf (tarray tuchar 33)) ::
                 (Etempvar _t2 (tptr tuchar)) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _buf (tarray tuchar 33))
                      (Econst_int (Int.repr 32) tint) (tptr tuchar)) tuchar)
                  (Econst_int (Int.repr 3) tint))
                (Scall None
                  (Evar _m_hmac (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
                  ((Etempvar _t3 (tptr tuchar)) ::
                   (Evar _prk (tarray tuchar 32)) ::
                   (Evar _buf (tarray tuchar 33)) ::
                   (Econst_int (Int.repr 33) tint) :: nil))))))))))
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

Definition v_x_handshake__M_BASEPOINT := {|
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
           (Evar _x_handshake__M_BASEPOINT (tarray tuchar 32)) :: nil))
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

Definition v_x_handshake__M_CONSTRUCTION := {|
  gvar_info := (tarray tuchar 37);
  gvar_init := (Init_int8 (Int.repr 78) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 101) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 73) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 112) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 107) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 53) :: Init_int8 (Int.repr 53) ::
                Init_int8 (Int.repr 49) :: Init_int8 (Int.repr 57) ::
                Init_int8 (Int.repr 95) :: Init_int8 (Int.repr 67) ::
                Init_int8 (Int.repr 104) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 67) :: Init_int8 (Int.repr 104) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 80) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 108) ::
                Init_int8 (Int.repr 121) :: Init_int8 (Int.repr 95) ::
                Init_int8 (Int.repr 66) :: Init_int8 (Int.repr 76) ::
                Init_int8 (Int.repr 65) :: Init_int8 (Int.repr 75) ::
                Init_int8 (Int.repr 69) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 115) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_handshake__M_IDENTIFIER := {|
  gvar_info := (tarray tuchar 34);
  gvar_init := (Init_int8 (Int.repr 87) :: Init_int8 (Int.repr 105) ::
                Init_int8 (Int.repr 114) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 71) :: Init_int8 (Int.repr 117) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 114) ::
                Init_int8 (Int.repr 100) :: Init_int8 (Int.repr 32) ::
                Init_int8 (Int.repr 118) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 32) :: Init_int8 (Int.repr 74) ::
                Init_int8 (Int.repr 97) :: Init_int8 (Int.repr 115) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 110) ::
                Init_int8 (Int.repr 64) :: Init_int8 (Int.repr 122) ::
                Init_int8 (Int.repr 120) :: Init_int8 (Int.repr 50) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 52) ::
                Init_int8 (Int.repr 46) :: Init_int8 (Int.repr 99) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 109) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_m_start := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_responder_pub, (tptr tuchar)) :: nil);
  fn_vars := ((_h0, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_hash2 (Tfunction
                     ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                      (tptr tuchar) :: tulong :: nil) tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Evar _x_handshake__M_CONSTRUCTION (tarray tuchar 37)) ::
     (Econst_int (Int.repr 37) tint) ::
     (Evar _x_handshake__M_CONSTRUCTION (tarray tuchar 37)) ::
     (Econst_int (Int.repr 0) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _m_hash2 (Tfunction
                       ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                        (tptr tuchar) :: tulong :: nil) tvoid cc_default))
      ((Evar _h0 (tarray tuchar 32)) ::
       (Efield
         (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) ::
       (Evar _x_handshake__M_IDENTIFIER (tarray tuchar 34)) ::
       (Econst_int (Int.repr 34) tint) :: nil))
    (Scall None
      (Evar _m_hash2 (Tfunction
                       ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                        (tptr tuchar) :: tulong :: nil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
       (Evar _h0 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
       (Etempvar _responder_pub (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))))
|}.

Definition f_m_mix_hash := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_d, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := ((_t, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_hash2 (Tfunction
                     ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                      (tptr tuchar) :: tulong :: nil) tvoid cc_default))
    ((Evar _t (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: (Etempvar _d (tptr tuchar)) ::
     (Etempvar _n tulong) :: nil))
  (Scall None
    (Evar _bytes_copy (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
     (Evar _t (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)))
|}.

Definition f_m_mix_ck := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_d, (tptr tuchar)) :: (_n, tulong) :: nil);
  fn_vars := ((_t1, (tarray tuchar 32)) :: (_t2, (tarray tuchar 32)) ::
              (_t3, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tvoid
                   cc_default))
    ((Evar _t1 (tarray tuchar 32)) :: (Evar _t2 (tarray tuchar 32)) ::
     (Evar _t3 (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Etempvar _d (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
  (Scall None
    (Evar _bytes_copy (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Evar _t1 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil)))
|}.

Definition f_m_mix_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_key, (tptr tuchar)) :: (_d, (tptr tuchar)) ::
                (_n, tulong) :: nil);
  fn_vars := ((_t1, (tarray tuchar 32)) :: (_t2, (tarray tuchar 32)) ::
              (_t3, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tvoid
                   cc_default))
    ((Evar _t1 (tarray tuchar 32)) :: (Evar _t2 (tarray tuchar 32)) ::
     (Evar _t3 (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Etempvar _d (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
       (Evar _t1 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Etempvar _key (tptr tuchar)) :: (Evar _t2 (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))))
|}.

Definition f_m_mix_psk := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_key, (tptr tuchar)) :: (_psk, (tptr tuchar)) :: nil);
  fn_vars := ((_t1, (tarray tuchar 32)) :: (_t2, (tarray tuchar 32)) ::
              (_t3, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tvoid
                   cc_default))
    ((Evar _t1 (tarray tuchar 32)) :: (Evar _t2 (tarray tuchar 32)) ::
     (Evar _t3 (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Etempvar _psk (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
       (Evar _t1 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Etempvar _key (tptr tuchar)) :: (Evar _t3 (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Scall None
        (Evar _m_mix_hash (Tfunction
                            ((tptr (Tstruct _m_state noattr)) ::
                             (tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
        ((Etempvar _s (tptr (Tstruct _m_state noattr))) ::
         (Evar _t2 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil)))))
|}.

Definition f_m_encrypt_and_hash := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_c, (tptr tuchar)) :: (_p, (tptr tuchar)) :: (_n, tulong) ::
                (_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _chacha20poly1305_encrypt (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       tulong :: (tptr tuchar) :: tulong ::
                                       tulong :: (tptr tuchar) :: nil) tvoid
                                      cc_default))
    ((Etempvar _c (tptr tuchar)) :: (Etempvar _p (tptr tuchar)) ::
     (Etempvar _n tulong) ::
     (Efield
       (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 0) tint) ::
     (Etempvar _key (tptr tuchar)) :: nil))
  (Scall None
    (Evar _m_mix_hash (Tfunction
                        ((tptr (Tstruct _m_state noattr)) :: (tptr tuchar) ::
                         tulong :: nil) tvoid cc_default))
    ((Etempvar _s (tptr (Tstruct _m_state noattr))) ::
     (Etempvar _c (tptr tuchar)) ::
     (Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 16) tint)
       tulong) :: nil)))
|}.

Definition f_m_decrypt_and_hash := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _m_state noattr))) ::
                (_p, (tptr tuchar)) :: (_c, (tptr tuchar)) :: (_n, tulong) ::
                (_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _chacha20poly1305_decrypt (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: (tptr tuchar) :: tulong ::
                                         tulong :: (tptr tuchar) :: nil)
                                        tbool cc_default))
      ((Etempvar _p (tptr tuchar)) :: (Etempvar _c (tptr tuchar)) ::
       (Etempvar _n tulong) ::
       (Efield
         (Ederef (Etempvar _s (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 0) tint) ::
       (Etempvar _key (tptr tuchar)) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _m_mix_hash (Tfunction
                          ((tptr (Tstruct _m_state noattr)) ::
                           (tptr tuchar) :: tulong :: nil) tvoid cc_default))
      ((Etempvar _s (tptr (Tstruct _m_state noattr))) ::
       (Etempvar _c (tptr tuchar)) :: (Etempvar _n tulong) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_m_tai64n := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_sec, tlong) :: (_nsec, tlong) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_s, tulong) :: (_n, tuint) :: (_i, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _s
    (Ebinop Oadd (Econst_long (Int64.repr 4611686018427387914) tulong)
      (Ecast (Etempvar _sec tlong) tulong) tulong))
  (Ssequence
    (Sset _n
      (Ecast
        (Ebinop Oand (Ecast (Etempvar _nsec tlong) tulong)
          (Eunop Onotint
            (Ebinop Osub (Ecast (Econst_int (Int.repr 16777216) tint) tulong)
              (Econst_int (Int.repr 1) tint) tulong) tulong) tulong) tuint))
    (Ssequence
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 8) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _out (tptr tuchar)) (Etempvar _i tint)
                  (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oshr (Etempvar _s tulong)
                  (Ebinop Osub (Econst_int (Int.repr 56) tint)
                    (Ebinop Omul (Econst_int (Int.repr 8) tint)
                      (Etempvar _i tint) tint) tint) tulong) tuchar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint))))
      (Ssequence
        (Sset _i (Econst_int (Int.repr 0) tint))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                           (Econst_int (Int.repr 4) tint) tint)
              Sskip
              Sbreak)
            (Sassign
              (Ederef
                (Ebinop Oadd (Etempvar _out (tptr tuchar))
                  (Ebinop Oadd (Econst_int (Int.repr 8) tint)
                    (Etempvar _i tint) tint) (tptr tuchar)) tuchar)
              (Ecast
                (Ebinop Oshr (Etempvar _n tuint)
                  (Ebinop Osub (Econst_int (Int.repr 24) tint)
                    (Ebinop Omul (Econst_int (Int.repr 8) tint)
                      (Etempvar _i tint) tint) tint) tuint) tuchar)))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint)
              tint)))))))
|}.

Definition f_m_create_initiation := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct _m_initiation noattr))) ::
                (_spub, (tptr tuchar)) :: (_rpub, (tptr tuchar)) ::
                (_ss, (tptr tuchar)) :: (_eraw, (tptr tuchar)) ::
                (_ts, (tptr tuchar)) :: nil);
  fn_vars := ((_key, (tarray tuchar 32)) :: (_dh, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_start (Tfunction
                     ((tptr (Tstruct _m_state noattr)) :: (tptr tuchar) ::
                      nil) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
           (Tstruct _m_initiation noattr)) _st (Tstruct _m_state noattr))
       (tptr (Tstruct _m_state noattr))) :: (Etempvar _rpub (tptr tuchar)) ::
     nil))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
           (Tstruct _m_initiation noattr)) _eph_priv (tarray tuchar 32)) ::
       (Etempvar _eraw (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _m_clamp (Tfunction ((tptr tuchar) :: nil) tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
             (Tstruct _m_initiation noattr)) _eph_priv (tarray tuchar 32)) ::
         nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _m_dh (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                           nil) tint cc_default))
            ((Efield
               (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                 (Tstruct _m_initiation noattr)) _ephemeral
               (tarray tuchar 32)) ::
             (Efield
               (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                 (Tstruct _m_initiation noattr)) _eph_priv
               (tarray tuchar 32)) ::
             (Evar _x_handshake__M_BASEPOINT (tarray tuchar 32)) :: nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Ssequence
          (Scall None
            (Evar _m_mix_hash (Tfunction
                                ((tptr (Tstruct _m_state noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                   (Tstruct _m_initiation noattr)) _st
                 (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
             (Efield
               (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                 (Tstruct _m_initiation noattr)) _ephemeral
               (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _m_mix_ck (Tfunction
                                ((tptr (Tstruct _m_state noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                     (Tstruct _m_initiation noattr)) _st
                   (Tstruct _m_state noattr))
                 (tptr (Tstruct _m_state noattr))) ::
               (Efield
                 (Ederef (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                   (Tstruct _m_initiation noattr)) _ephemeral
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _m_dh (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) ::
                                 (tptr tuchar) :: nil) tint cc_default))
                  ((Evar _dh (tarray tuchar 32)) ::
                   (Efield
                     (Ederef
                       (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                       (Tstruct _m_initiation noattr)) _eph_priv
                     (tarray tuchar 32)) :: (Etempvar _rpub (tptr tuchar)) ::
                   nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Scall None
                  (Evar _m_mix_key (Tfunction
                                     ((tptr (Tstruct _m_state noattr)) ::
                                      (tptr tuchar) :: (tptr tuchar) ::
                                      tulong :: nil) tvoid cc_default))
                  ((Eaddrof
                     (Efield
                       (Ederef
                         (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                         (Tstruct _m_initiation noattr)) _st
                       (Tstruct _m_state noattr))
                     (tptr (Tstruct _m_state noattr))) ::
                   (Evar _key (tarray tuchar 32)) ::
                   (Evar _dh (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _m_encrypt_and_hash (Tfunction
                                                ((tptr (Tstruct _m_state noattr)) ::
                                                 (tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 (tptr tuchar) :: nil) tvoid
                                                cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                           (Tstruct _m_initiation noattr)) _st
                         (Tstruct _m_state noattr))
                       (tptr (Tstruct _m_state noattr))) ::
                     (Efield
                       (Ederef
                         (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                         (Tstruct _m_initiation noattr)) _enc_static
                       (tarray tuchar 48)) ::
                     (Etempvar _spub (tptr tuchar)) ::
                     (Econst_int (Int.repr 32) tint) ::
                     (Evar _key (tarray tuchar 32)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _bytes_zero (Tfunction
                                            ((tptr tuchar) :: tulong :: nil)
                                            tint cc_default))
                        ((Etempvar _ss (tptr tuchar)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Sifthenelse (Etempvar _t'3 tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        Sskip))
                    (Ssequence
                      (Scall None
                        (Evar _m_mix_key (Tfunction
                                           ((tptr (Tstruct _m_state noattr)) ::
                                            (tptr tuchar) :: (tptr tuchar) ::
                                            tulong :: nil) tvoid cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                               (Tstruct _m_initiation noattr)) _st
                             (Tstruct _m_state noattr))
                           (tptr (Tstruct _m_state noattr))) ::
                         (Evar _key (tarray tuchar 32)) ::
                         (Etempvar _ss (tptr tuchar)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _m_encrypt_and_hash (Tfunction
                                                      ((tptr (Tstruct _m_state noattr)) ::
                                                       (tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong ::
                                                       (tptr tuchar) :: nil)
                                                      tvoid cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                                 (Tstruct _m_initiation noattr)) _st
                               (Tstruct _m_state noattr))
                             (tptr (Tstruct _m_state noattr))) ::
                           (Efield
                             (Ederef
                               (Etempvar _o (tptr (Tstruct _m_initiation noattr)))
                               (Tstruct _m_initiation noattr)) _enc_timestamp
                             (tarray tuchar 28)) ::
                           (Etempvar _ts (tptr tuchar)) ::
                           (Econst_int (Int.repr 12) tint) ::
                           (Evar _key (tarray tuchar 32)) :: nil))
                        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))))))
|}.

Definition f_m_consume_initiation_1 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct _m_consumed_initiation noattr))) ::
                (_rid, (tptr (Tstruct _m_identity noattr))) ::
                (_ephemeral, (tptr tuchar)) ::
                (_enc_static, (tptr tuchar)) :: nil);
  fn_vars := ((_dh, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _m_start (Tfunction
                     ((tptr (Tstruct _m_state noattr)) :: (tptr tuchar) ::
                      nil) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
           (Tstruct _m_consumed_initiation noattr)) _st
         (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
     (Efield
       (Ederef (Etempvar _rid (tptr (Tstruct _m_identity noattr)))
         (Tstruct _m_identity noattr)) _pub (tarray tuchar 32)) :: nil))
  (Ssequence
    (Scall None
      (Evar _m_mix_hash (Tfunction
                          ((tptr (Tstruct _m_state noattr)) ::
                           (tptr tuchar) :: tulong :: nil) tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef
             (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
             (Tstruct _m_consumed_initiation noattr)) _st
           (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
       (Etempvar _ephemeral (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _m_mix_ck (Tfunction
                          ((tptr (Tstruct _m_state noattr)) ::
                           (tptr tuchar) :: tulong :: nil) tvoid cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
               (Tstruct _m_consumed_initiation noattr)) _st
             (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
         (Etempvar _ephemeral (tptr tuchar)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _m_dh (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                           nil) tint cc_default))
            ((Evar _dh (tarray tuchar 32)) ::
             (Efield
               (Ederef (Etempvar _rid (tptr (Tstruct _m_identity noattr)))
                 (Tstruct _m_identity noattr)) _priv (tarray tuchar 32)) ::
             (Etempvar _ephemeral (tptr tuchar)) :: nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
            (Sreturn (Some (Econst_int (Int.repr 0) tint)))
            Sskip))
        (Ssequence
          (Scall None
            (Evar _m_mix_key (Tfunction
                               ((tptr (Tstruct _m_state noattr)) ::
                                (tptr tuchar) :: (tptr tuchar) :: tulong ::
                                nil) tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef
                   (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
                   (Tstruct _m_consumed_initiation noattr)) _st
                 (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
             (Efield
               (Ederef
                 (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
                 (Tstruct _m_consumed_initiation noattr)) _key
               (tarray tuchar 32)) :: (Evar _dh (tarray tuchar 32)) ::
             (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Scall (Some _t'2)
              (Evar _m_decrypt_and_hash (Tfunction
                                          ((tptr (Tstruct _m_state noattr)) ::
                                           (tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: (tptr tuchar) :: nil)
                                          tint cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
                     (Tstruct _m_consumed_initiation noattr)) _st
                   (Tstruct _m_state noattr))
                 (tptr (Tstruct _m_state noattr))) ::
               (Efield
                 (Ederef
                   (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
                   (Tstruct _m_consumed_initiation noattr)) _spub
                 (tarray tuchar 32)) ::
               (Etempvar _enc_static (tptr tuchar)) ::
               (Econst_int (Int.repr 48) tint) ::
               (Efield
                 (Ederef
                   (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
                   (Tstruct _m_consumed_initiation noattr)) _key
                 (tarray tuchar 32)) :: nil))
            (Sreturn (Some (Etempvar _t'2 tint)))))))))
|}.

Definition f_m_consume_initiation_2 := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct _m_consumed_initiation noattr))) ::
                (_ss, (tptr tuchar)) :: (_enc_timestamp, (tptr tuchar)) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _bytes_zero (Tfunction ((tptr tuchar) :: tulong :: nil) tint
                          cc_default))
      ((Etempvar _ss (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _m_mix_key (Tfunction
                         ((tptr (Tstruct _m_state noattr)) ::
                          (tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                         tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef
             (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
             (Tstruct _m_consumed_initiation noattr)) _st
           (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
       (Efield
         (Ederef (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
           (Tstruct _m_consumed_initiation noattr)) _key (tarray tuchar 32)) ::
       (Etempvar _ss (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _m_decrypt_and_hash (Tfunction
                                    ((tptr (Tstruct _m_state noattr)) ::
                                     (tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: (tptr tuchar) :: nil) tint
                                    cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
               (Tstruct _m_consumed_initiation noattr)) _st
             (Tstruct _m_state noattr)) (tptr (Tstruct _m_state noattr))) ::
         (Efield
           (Ederef
             (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
             (Tstruct _m_consumed_initiation noattr)) _ts (tarray tuchar 12)) ::
         (Etempvar _enc_timestamp (tptr tuchar)) ::
         (Econst_int (Int.repr 28) tint) ::
         (Efield
           (Ederef
             (Etempvar _o (tptr (Tstruct _m_consumed_initiation noattr)))
             (Tstruct _m_consumed_initiation noattr)) _key
           (tarray tuchar 32)) :: nil))
      (Sreturn (Some (Etempvar _t'2 tint))))))
|}.

Definition f_m_create_response := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_o, (tptr (Tstruct _m_response noattr))) ::
                (_st, (tptr (Tstruct _m_state noattr))) ::
                (_ei, (tptr tuchar)) :: (_si, (tptr tuchar)) ::
                (_psk, (tptr tuchar)) :: (_eraw, (tptr tuchar)) :: nil);
  fn_vars := ((_dh, (tarray tuchar 32)) :: (_key, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _bytes_copy (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
    ((Efield
       (Efield
         (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
           (Tstruct _m_response noattr)) _st (Tstruct _m_state noattr)) _ck
       (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _st (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Efield
           (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
             (Tstruct _m_response noattr)) _st (Tstruct _m_state noattr)) _h
         (tarray tuchar 32)) ::
       (Efield
         (Ederef (Etempvar _st (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Efield
           (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
             (Tstruct _m_response noattr)) _eph_priv (tarray tuchar 32)) ::
         (Etempvar _eraw (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Ssequence
        (Scall None
          (Evar _m_clamp (Tfunction ((tptr tuchar) :: nil) tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
               (Tstruct _m_response noattr)) _eph_priv (tarray tuchar 32)) ::
           nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _m_dh (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) ::
                             (tptr tuchar) :: nil) tint cc_default))
              ((Efield
                 (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
                   (Tstruct _m_response noattr)) _ephemeral
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
                   (Tstruct _m_response noattr)) _eph_priv
                 (tarray tuchar 32)) ::
               (Evar _x_handshake__M_BASEPOINT (tarray tuchar 32)) :: nil))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _m_mix_hash (Tfunction
                                  ((tptr (Tstruct _m_state noattr)) ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
                     (Tstruct _m_response noattr)) _st
                   (Tstruct _m_state noattr))
                 (tptr (Tstruct _m_state noattr))) ::
               (Efield
                 (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
                   (Tstruct _m_response noattr)) _ephemeral
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))
            (Ssequence
              (Scall None
                (Evar _m_mix_ck (Tfunction
                                  ((tptr (Tstruct _m_state noattr)) ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef
                       (Etempvar _o (tptr (Tstruct _m_response noattr)))
                       (Tstruct _m_response noattr)) _st
                     (Tstruct _m_state noattr))
                   (tptr (Tstruct _m_state noattr))) ::
                 (Efield
                   (Ederef (Etempvar _o (tptr (Tstruct _m_response noattr)))
                     (Tstruct _m_response noattr)) _ephemeral
                   (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
                 nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _m_dh (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   (tptr tuchar) :: nil) tint cc_default))
                    ((Evar _dh (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _o (tptr (Tstruct _m_response noattr)))
                         (Tstruct _m_response noattr)) _eph_priv
                       (tarray tuchar 32)) :: (Etempvar _ei (tptr tuchar)) ::
                     nil))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip))
                (Ssequence
                  (Scall None
                    (Evar _m_mix_ck (Tfunction
                                      ((tptr (Tstruct _m_state noattr)) ::
                                       (tptr tuchar) :: tulong :: nil) tvoid
                                      cc_default))
                    ((Eaddrof
                       (Efield
                         (Ederef
                           (Etempvar _o (tptr (Tstruct _m_response noattr)))
                           (Tstruct _m_response noattr)) _st
                         (Tstruct _m_state noattr))
                       (tptr (Tstruct _m_state noattr))) ::
                     (Evar _dh (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'3)
                        (Evar _m_dh (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       (tptr tuchar) :: nil) tint cc_default))
                        ((Evar _dh (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _o (tptr (Tstruct _m_response noattr)))
                             (Tstruct _m_response noattr)) _eph_priv
                           (tarray tuchar 32)) ::
                         (Etempvar _si (tptr tuchar)) :: nil))
                      (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint) tint)
                        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                        Sskip))
                    (Ssequence
                      (Scall None
                        (Evar _m_mix_ck (Tfunction
                                          ((tptr (Tstruct _m_state noattr)) ::
                                           (tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _o (tptr (Tstruct _m_response noattr)))
                               (Tstruct _m_response noattr)) _st
                             (Tstruct _m_state noattr))
                           (tptr (Tstruct _m_state noattr))) ::
                         (Evar _dh (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _m_mix_psk (Tfunction
                                             ((tptr (Tstruct _m_state noattr)) ::
                                              (tptr tuchar) ::
                                              (tptr tuchar) :: nil) tvoid
                                             cc_default))
                          ((Eaddrof
                             (Efield
                               (Ederef
                                 (Etempvar _o (tptr (Tstruct _m_response noattr)))
                                 (Tstruct _m_response noattr)) _st
                               (Tstruct _m_state noattr))
                             (tptr (Tstruct _m_state noattr))) ::
                           (Evar _key (tarray tuchar 32)) ::
                           (Etempvar _psk (tptr tuchar)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _m_encrypt_and_hash (Tfunction
                                                        ((tptr (Tstruct _m_state noattr)) ::
                                                         (tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         tulong ::
                                                         (tptr tuchar) ::
                                                         nil) tvoid
                                                        cc_default))
                            ((Eaddrof
                               (Efield
                                 (Ederef
                                   (Etempvar _o (tptr (Tstruct _m_response noattr)))
                                   (Tstruct _m_response noattr)) _st
                                 (Tstruct _m_state noattr))
                               (tptr (Tstruct _m_state noattr))) ::
                             (Efield
                               (Ederef
                                 (Etempvar _o (tptr (Tstruct _m_response noattr)))
                                 (Tstruct _m_response noattr)) _enc_nothing
                               (tarray tuchar 16)) ::
                             (Evar _x_handshake__M_BASEPOINT (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Evar _key (tarray tuchar 32)) :: nil))
                          (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))))))))
|}.

Definition f_m_consume_response := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr (Tstruct _m_state noattr))) ::
                (_st, (tptr (Tstruct _m_state noattr))) ::
                (_eph_priv, (tptr tuchar)) :: (_spriv, (tptr tuchar)) ::
                (_psk, (tptr tuchar)) :: (_ephemeral, (tptr tuchar)) ::
                (_enc_nothing, (tptr tuchar)) :: nil);
  fn_vars := ((_dh, (tarray tuchar 32)) :: (_key, (tarray tuchar 32)) ::
              (_nothing, (tarray tuchar 1)) :: nil);
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _bytes_copy (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
    ((Efield
       (Ederef (Etempvar _out (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Efield
       (Ederef (Etempvar _st (tptr (Tstruct _m_state noattr)))
         (Tstruct _m_state noattr)) _ck (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _out (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
       (Efield
         (Ederef (Etempvar _st (tptr (Tstruct _m_state noattr)))
           (Tstruct _m_state noattr)) _h (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _m_mix_hash (Tfunction
                            ((tptr (Tstruct _m_state noattr)) ::
                             (tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
        ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
         (Etempvar _ephemeral (tptr tuchar)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _m_mix_ck (Tfunction
                            ((tptr (Tstruct _m_state noattr)) ::
                             (tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
          ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
           (Etempvar _ephemeral (tptr tuchar)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _m_dh (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) ::
                             (tptr tuchar) :: nil) tint cc_default))
              ((Evar _dh (tarray tuchar 32)) ::
               (Etempvar _eph_priv (tptr tuchar)) ::
               (Etempvar _ephemeral (tptr tuchar)) :: nil))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
              (Sreturn (Some (Econst_int (Int.repr 0) tint)))
              Sskip))
          (Ssequence
            (Scall None
              (Evar _m_mix_ck (Tfunction
                                ((tptr (Tstruct _m_state noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
              ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
               (Evar _dh (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _m_dh (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) ::
                                 (tptr tuchar) :: nil) tint cc_default))
                  ((Evar _dh (tarray tuchar 32)) ::
                   (Etempvar _spriv (tptr tuchar)) ::
                   (Etempvar _ephemeral (tptr tuchar)) :: nil))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tint) tint)
                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                  Sskip))
              (Ssequence
                (Scall None
                  (Evar _m_mix_ck (Tfunction
                                    ((tptr (Tstruct _m_state noattr)) ::
                                     (tptr tuchar) :: tulong :: nil) tvoid
                                    cc_default))
                  ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
                   (Evar _dh (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _m_mix_psk (Tfunction
                                       ((tptr (Tstruct _m_state noattr)) ::
                                        (tptr tuchar) :: (tptr tuchar) ::
                                        nil) tvoid cc_default))
                    ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
                     (Evar _key (tarray tuchar 32)) ::
                     (Etempvar _psk (tptr tuchar)) :: nil))
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _m_decrypt_and_hash (Tfunction
                                                  ((tptr (Tstruct _m_state noattr)) ::
                                                   (tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   (tptr tuchar) :: nil) tint
                                                  cc_default))
                      ((Etempvar _out (tptr (Tstruct _m_state noattr))) ::
                       (Evar _nothing (tarray tuchar 1)) ::
                       (Etempvar _enc_nothing (tptr tuchar)) ::
                       (Econst_int (Int.repr 16) tint) ::
                       (Evar _key (tarray tuchar 32)) :: nil))
                    (Sreturn (Some (Etempvar _t'3 tint)))))))))))))
|}.

Definition f_m_transport := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_first, (tptr tuchar)) :: (_second, (tptr tuchar)) ::
                (_ck, (tptr tuchar)) :: nil);
  fn_vars := ((_t3, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _m_kdf (Tfunction
                 ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                  (tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tvoid
                 cc_default))
  ((Etempvar _first (tptr tuchar)) :: (Etempvar _second (tptr tuchar)) ::
   (Evar _t3 (tarray tuchar 32)) :: (Etempvar _ck (tptr tuchar)) ::
   (Evar _x_handshake__M_BASEPOINT (tarray tuchar 32)) ::
   (Econst_int (Int.repr 0) tint) :: nil))
|}.

Definition v_x_handshake__M_LABEL_MAC1 := {|
  gvar_info := (tarray tuchar 8);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_x_handshake__M_LABEL_COOKIE := {|
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

Definition f_m_precomputed := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) ::
                (_id, (tptr (Tstruct _m_identity noattr))) ::
                (_peer_pub, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tint) :: (_t'3, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
          (Tstruct _m_identity noattr)) _ok tint))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tint) tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Scall (Some _t'2)
          (Evar _m_dh (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                         nil) tint cc_default))
          ((Etempvar _out (tptr tuchar)) ::
           (Efield
             (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
               (Tstruct _m_identity noattr)) _priv (tarray tuchar 32)) ::
           (Etempvar _peer_pub (tptr tuchar)) :: nil))
        (Sset _t'1 (Ecast (Eunop Onotbool (Etempvar _t'2 tint) tint) tbool)))))
  (Sifthenelse (Etempvar _t'1 tint)
    (Scall None
      (Evar _bytes_set (Tfunction ((tptr tuchar) :: tuchar :: tulong :: nil)
                         tvoid cc_default))
      ((Etempvar _out (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    Sskip))
|}.

Definition f_table_has := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _index_hashtable noattr))) ::
                (_e, (tptr (Tstruct _index_hashtable_entry noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_it, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_n, tint) :: (_t'1, tint) :: (_t'2, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _it
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _index_hashtable noattr)))
            (Tstruct _index_hashtable noattr)) _head
          (tptr (Tstruct _index_hashtable_entry noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
            Sskip
            Sbreak)
          (Sifthenelse (Ebinop Oeq
                         (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
                         (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                         tint)
            (Sset _n
              (Ebinop Oadd (Etempvar _n tint) (Econst_int (Int.repr 1) tint)
                tint))
            Sskip))
        (Sset _it
          (Efield
            (Ederef
              (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr))))))
    (Ssequence
      (Sifthenelse (Ebinop Oeq (Etempvar _n tint)
                     (Econst_int (Int.repr 1) tint) tint)
        (Ssequence
          (Sset _t'2
            (Efield
              (Ederef
                (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
          (Sset _t'1 (Ecast (Etempvar _t'2 tbool) tbool)))
        (Sset _t'1 (Econst_int (Int.repr 0) tint)))
      (Sreturn (Some (Etempvar _t'1 tint))))))
|}.

Definition f_table_index_unique := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _index_hashtable noattr))) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_it, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_n, tint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Ssequence
      (Sset _it
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _index_hashtable noattr)))
            (Tstruct _index_hashtable noattr)) _head
          (tptr (Tstruct _index_hashtable_entry noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _index tuint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                           (Etempvar _index tuint) tint)
              (Sset _n
                (Ebinop Oadd (Etempvar _n tint)
                  (Econst_int (Int.repr 1) tint) tint))
              Sskip)))
        (Sset _it
          (Efield
            (Ederef
              (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr))))))
    (Sreturn (Some (Ebinop Oeq (Etempvar _n tint)
                     (Econst_int (Int.repr 1) tint) tint)))))
|}.

Definition f_table_len := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr (Tstruct _index_hashtable noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_it, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_n, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Ssequence
      (Sset _it
        (Efield
          (Ederef (Etempvar _t (tptr (Tstruct _index_hashtable noattr)))
            (Tstruct _index_hashtable noattr)) _head
          (tptr (Tstruct _index_hashtable_entry noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
            Sskip
            Sbreak)
          (Sset _n
            (Ebinop Oadd (Etempvar _n tulong) (Econst_int (Int.repr 1) tint)
              tulong)))
        (Sset _it
          (Efield
            (Ederef
              (Etempvar _it (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr))))))
    (Sreturn (Some (Etempvar _n tulong)))))
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

Definition f_hs_zeroed_from := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _hs_snap noattr))) ::
                (_h, (tptr (Tstruct _noise_handshake noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'21, tint) :: (_t'20, tint) :: (_t'19, tint) ::
               (_t'18, tint) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, tint) :: (_t'4, tint) ::
               (_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'31, tuint) :: (_t'30, tint) ::
               (_t'29, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'28, (tptr (Tstruct _wg_peer noattr))) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tulong) :: (_t'24, tulong) ::
               (_t'23, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'22, (tptr (Tstruct _noise_static_identity noattr))) ::
               nil);
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
                            (Sset _t'30
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                  (Tstruct _noise_handshake noattr)) _state
                                tint))
                            (Sifthenelse (Ebinop Oeq (Etempvar _t'30 tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint)
                              (Ssequence
                                (Sset _t'31
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                      (Tstruct _noise_handshake noattr))
                                    _remote_index tuint))
                                (Sset _t'1
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _t'31 tuint)
                                      (Econst_int (Int.repr 0) tint) tint)
                                    tbool)))
                              (Sset _t'1 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'1 tint)
                            (Ssequence
                              (Scall (Some _t'3)
                                (Evar _bytes_zero (Tfunction
                                                    ((tptr tuchar) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                                ((Efield
                                   (Ederef
                                     (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                     (Tstruct _noise_handshake noattr))
                                   _ephemeral_private (tarray tuchar 32)) ::
                                 (Econst_int (Int.repr 32) tint) :: nil))
                              (Sset _t'2 (Ecast (Etempvar _t'3 tint) tbool)))
                            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'2 tint)
                          (Ssequence
                            (Scall (Some _t'5)
                              (Evar _bytes_zero (Tfunction
                                                  ((tptr tuchar) :: tulong ::
                                                   nil) tint cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr))
                                 _remote_ephemeral (tarray tuchar 32)) ::
                               (Econst_int (Int.repr 32) tint) :: nil))
                            (Sset _t'4 (Ecast (Etempvar _t'5 tint) tbool)))
                          (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'4 tint)
                        (Ssequence
                          (Scall (Some _t'7)
                            (Evar _bytes_zero (Tfunction
                                                ((tptr tuchar) :: tulong ::
                                                 nil) tint cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr)) _hash
                               (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Sset _t'6 (Ecast (Etempvar _t'7 tint) tbool)))
                        (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'6 tint)
                      (Ssequence
                        (Scall (Some _t'9)
                          (Evar _bytes_zero (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tint cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _chaining_key (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Sset _t'8 (Ecast (Etempvar _t'9 tint) tbool)))
                      (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'8 tint)
                    (Ssequence
                      (Sset _t'28
                        (Efield
                          (Ederef
                            (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                            (Tstruct _hs_snap noattr)) _peer
                          (tptr (Tstruct _wg_peer noattr))))
                      (Ssequence
                        (Sset _t'29
                          (Efield
                            (Efield
                              (Ederef
                                (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                (Tstruct _noise_handshake noattr)) _entry
                              (Tstruct _index_hashtable_entry noattr)) _peer
                            (tptr (Tstruct _wg_peer noattr))))
                        (Sset _t'10
                          (Ecast
                            (Ebinop Oeq
                              (Etempvar _t'28 (tptr (Tstruct _wg_peer noattr)))
                              (Etempvar _t'29 (tptr (Tstruct _wg_peer noattr)))
                              tint) tbool))))
                    (Sset _t'10 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'10 tint)
                  (Ssequence
                    (Sset _t'26
                      (Efield
                        (Ederef
                          (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                          (Tstruct _hs_snap noattr)) _type tint))
                    (Ssequence
                      (Sset _t'27
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                              (Tstruct _noise_handshake noattr)) _entry
                            (Tstruct _index_hashtable_entry noattr)) _type
                          tint))
                      (Sset _t'11
                        (Ecast
                          (Ebinop Oeq (Etempvar _t'26 tint)
                            (Etempvar _t'27 tint) tint) tbool))))
                  (Sset _t'11 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'11 tint)
                (Ssequence
                  (Sset _t'24
                    (Efield
                      (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                        (Tstruct _hs_snap noattr))
                      _last_initiation_consumption tulong))
                  (Ssequence
                    (Sset _t'25
                      (Efield
                        (Ederef
                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                          (Tstruct _noise_handshake noattr))
                        _last_initiation_consumption tulong))
                    (Sset _t'12
                      (Ecast
                        (Ebinop Oeq (Etempvar _t'24 tulong)
                          (Etempvar _t'25 tulong) tint) tbool))))
                (Sset _t'12 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'12 tint)
              (Ssequence
                (Sset _t'22
                  (Efield
                    (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                      (Tstruct _hs_snap noattr)) _static_identity
                    (tptr (Tstruct _noise_static_identity noattr))))
                (Ssequence
                  (Sset _t'23
                    (Efield
                      (Ederef
                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                        (Tstruct _noise_handshake noattr)) _static_identity
                      (tptr (Tstruct _noise_static_identity noattr))))
                  (Sset _t'13
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _t'22 (tptr (Tstruct _noise_static_identity noattr)))
                        (Etempvar _t'23 (tptr (Tstruct _noise_static_identity noattr)))
                        tint) tbool))))
              (Sset _t'13 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'13 tint)
            (Ssequence
              (Scall (Some _t'15)
                (Evar _bytes_eq (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tint cc_default))
                ((Efield
                   (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                     (Tstruct _hs_snap noattr)) _remote_static
                   (tarray tuchar 32)) ::
                 (Efield
                   (Ederef
                     (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                     (Tstruct _noise_handshake noattr)) _remote_static
                   (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
                 nil))
              (Sset _t'14 (Ecast (Etempvar _t'15 tint) tbool)))
            (Sset _t'14 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'14 tint)
          (Ssequence
            (Scall (Some _t'17)
              (Evar _bytes_eq (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tint cc_default))
              ((Efield
                 (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                   (Tstruct _hs_snap noattr)) _precomputed_static_static
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef
                   (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr))
                 _precomputed_static_static (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Sset _t'16 (Ecast (Etempvar _t'17 tint) tbool)))
          (Sset _t'16 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'16 tint)
        (Ssequence
          (Scall (Some _t'19)
            (Evar _bytes_eq (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tint cc_default))
            ((Efield
               (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                 (Tstruct _hs_snap noattr)) _preshared_key
               (tarray tuchar 32)) ::
             (Efield
               (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                 (Tstruct _noise_handshake noattr)) _preshared_key
               (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Sset _t'18 (Ecast (Etempvar _t'19 tint) tbool)))
        (Sset _t'18 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'18 tint)
      (Ssequence
        (Scall (Some _t'21)
          (Evar _bytes_eq (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tint cc_default))
          ((Efield
             (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
               (Tstruct _hs_snap noattr)) _latest_timestamp
             (tarray tuchar 12)) ::
           (Efield
             (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
               (Tstruct _noise_handshake noattr)) _latest_timestamp
             (tarray tuchar 12)) :: (Econst_int (Int.repr 12) tint) :: nil))
        (Sset _t'20 (Ecast (Etempvar _t'21 tint) tbool)))
      (Sset _t'20 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'20 tint))))
|}.

Definition f_m_static_public_field := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) ::
                (_id, (tptr (Tstruct _m_identity noattr))) ::
                (_raw, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _bytes_zero (Tfunction ((tptr tuchar) :: tulong :: nil) tint
                        cc_default))
    ((Etempvar _raw (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) :: nil))
  (Sifthenelse (Etempvar _t'1 tint)
    (Scall None
      (Evar _bytes_set (Tfunction ((tptr tuchar) :: tuchar :: tulong :: nil)
                         tvoid cc_default))
      ((Etempvar _out (tptr tuchar)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Scall None
      (Evar _bytes_copy (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                          tvoid cc_default))
      ((Etempvar _out (tptr tuchar)) ::
       (Efield
         (Ederef (Etempvar _id (tptr (Tstruct _m_identity noattr)))
           (Tstruct _m_identity noattr)) _pub (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))))
|}.

Definition f_init_img := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_img, (tptr tuchar)) ::
                (_m, (tptr (Tstruct _message_handshake_initiation noattr))) ::
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
            (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _header
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
            (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _sender_index
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
             (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
             (Tstruct _message_handshake_initiation noattr))
           _unencrypted_ephemeral (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _bytes_copy (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tvoid cc_default))
          ((Ebinop Oadd (Etempvar _img (tptr tuchar))
             (Econst_int (Int.repr 40) tint) (tptr tuchar)) ::
           (Efield
             (Ederef
               (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
               (Tstruct _message_handshake_initiation noattr))
             _encrypted_static (tarray tuchar 48)) ::
           (Econst_int (Int.repr 48) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Ebinop Oadd (Etempvar _img (tptr tuchar))
               (Econst_int (Int.repr 88) tint) (tptr tuchar)) ::
             (Efield
               (Ederef
                 (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                 (Tstruct _message_handshake_initiation noattr))
               _encrypted_timestamp (tarray tuchar 28)) ::
             (Econst_int (Int.repr 28) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Ebinop Oadd (Etempvar _img (tptr tuchar))
                 (Econst_int (Int.repr 116) tint) (tptr tuchar)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Ebinop Oadd (Etempvar _img (tptr tuchar))
                 (Econst_int (Int.repr 132) tint) (tptr tuchar)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))))))))
|}.

Definition f_resp_img := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_img, (tptr tuchar)) ::
                (_m, (tptr (Tstruct _message_handshake_response noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
            (Tstruct _message_handshake_response noattr)) _header
          (Tstruct _message_header noattr)) _type tuint))
    (Scall None
      (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                          cc_default))
      ((Etempvar _img (tptr tuchar)) :: (Etempvar _t'3 tuint) :: nil)))
  (Ssequence
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
            (Tstruct _message_handshake_response noattr)) _sender_index
          tuint))
      (Scall None
        (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                            cc_default))
        ((Ebinop Oadd (Etempvar _img (tptr tuchar))
           (Econst_int (Int.repr 4) tint) (tptr tuchar)) ::
         (Etempvar _t'2 tuint) :: nil)))
    (Ssequence
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef
              (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
              (Tstruct _message_handshake_response noattr)) _receiver_index
            tuint))
        (Scall None
          (Evar _le32_store (Tfunction ((tptr tuchar) :: tuint :: nil) tvoid
                              cc_default))
          ((Ebinop Oadd (Etempvar _img (tptr tuchar))
             (Econst_int (Int.repr 8) tint) (tptr tuchar)) ::
           (Etempvar _t'1 tuint) :: nil)))
      (Ssequence
        (Scall None
          (Evar _bytes_copy (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tvoid cc_default))
          ((Ebinop Oadd (Etempvar _img (tptr tuchar))
             (Econst_int (Int.repr 12) tint) (tptr tuchar)) ::
           (Efield
             (Ederef
               (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
               (Tstruct _message_handshake_response noattr))
             _unencrypted_ephemeral (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Ebinop Oadd (Etempvar _img (tptr tuchar))
               (Econst_int (Int.repr 44) tint) (tptr tuchar)) ::
             (Efield
               (Ederef
                 (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                 (Tstruct _message_handshake_response noattr))
               _encrypted_nothing (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Ebinop Oadd (Etempvar _img (tptr tuchar))
                 (Econst_int (Int.repr 60) tint) (tptr tuchar)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                     (Tstruct _message_handshake_response noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Ebinop Oadd (Etempvar _img (tptr tuchar))
                 (Econst_int (Int.repr 76) tint) (tptr tuchar)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                     (Tstruct _message_handshake_response noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))))))))
|}.

Definition f_fill_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _message_handshake_initiation noattr))) ::
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
            (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _header
          (Tstruct _message_header noattr)) _type tuint)
      (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sassign
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _sender_index
          tuint) (Etempvar _t'2 tuint)))
    (Ssequence
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Efield
           (Ederef
             (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
             (Tstruct _message_handshake_initiation noattr))
           _unencrypted_ephemeral (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Efield
             (Ederef
               (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
               (Tstruct _message_handshake_initiation noattr))
             _encrypted_static (tarray tuchar 48)) ::
           (Econst_int (Int.repr 48) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
            ((Efield
               (Ederef
                 (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                 (Tstruct _message_handshake_initiation noattr))
               _encrypted_timestamp (tarray tuchar 28)) ::
             (Econst_int (Int.repr 28) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))))))))
|}.

Definition f_fill_resp := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_m, (tptr (Tstruct _message_handshake_response noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sassign
      (Efield
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
            (Tstruct _message_handshake_response noattr)) _header
          (Tstruct _message_header noattr)) _type tuint)
      (Etempvar _t'1 tuint)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sassign
        (Efield
          (Ederef
            (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
            (Tstruct _message_handshake_response noattr)) _sender_index
          tuint) (Etempvar _t'2 tuint)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'3)
          (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
        (Sassign
          (Efield
            (Ederef
              (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
              (Tstruct _message_handshake_response noattr)) _receiver_index
            tuint) (Etempvar _t'3 tuint)))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Efield
             (Ederef
               (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
               (Tstruct _message_handshake_response noattr))
             _unencrypted_ephemeral (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
            ((Efield
               (Ederef
                 (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                 (Tstruct _message_handshake_response noattr))
               _encrypted_nothing (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                     (Tstruct _message_handshake_response noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef
                     (Etempvar _m (tptr (Tstruct _message_handshake_response noattr)))
                     (Tstruct _message_handshake_response noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))))))))
|}.

Definition f_draw_real_clock := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _draw_u64 (Tfunction nil tulong cc_default))
      nil)
    (Sassign (Evar _wg_shim_real_sec tlong)
      (Ecast (Etempvar _t'1 tulong) tlong)))
  (Ssequence
    (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sassign (Evar _wg_shim_real_nsec tlong)
      (Ecast
        (Ebinop Omod (Etempvar _t'2 tuint)
          (Econst_int (Int.repr 1000000000) tuint) tuint) tlong))))
|}.

Definition f_m_ts_newer := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_t, (tptr tuchar)) :: (_latest, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tint) :: (_t'4, tuchar) :: (_t'3, tuchar) ::
               (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _i (Econst_int (Int.repr 0) tint))
    (Sloop
      (Ssequence
        (Sifthenelse (Ebinop Olt (Etempvar _i tint)
                       (Econst_int (Int.repr 12) tint) tint)
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Ederef
              (Ebinop Oadd (Etempvar _t (tptr tuchar)) (Etempvar _i tint)
                (tptr tuchar)) tuchar))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Ebinop Oadd (Etempvar _latest (tptr tuchar))
                  (Etempvar _i tint) (tptr tuchar)) tuchar))
            (Sifthenelse (Ebinop One (Etempvar _t'1 tuchar)
                           (Etempvar _t'2 tuchar) tint)
              (Ssequence
                (Sset _t'3
                  (Ederef
                    (Ebinop Oadd (Etempvar _t (tptr tuchar))
                      (Etempvar _i tint) (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'4
                    (Ederef
                      (Ebinop Oadd (Etempvar _latest (tptr tuchar))
                        (Etempvar _i tint) (tptr tuchar)) tuchar))
                  (Sreturn (Some (Ebinop Ogt (Etempvar _t'3 tuchar)
                                   (Etempvar _t'4 tuchar) tint)))))
              Sskip))))
      (Sset _i
        (Ebinop Oadd (Etempvar _i tint) (Econst_int (Int.repr 1) tint) tint))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_m_not_flood := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_last, tulong) :: (_now, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Eunop Onotbool
                 (Ebinop Ogt
                   (Ebinop Oadd (Ecast (Etempvar _last tulong) tlong)
                     (Econst_int (Int.repr 20000000) tint) tlong)
                   (Ecast (Etempvar _now tulong) tlong) tint) tint)))
|}.

Definition f_m_last_consumption := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_last, tulong) :: (_now, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop Olt
                 (Ecast
                   (Ebinop Osub (Etempvar _last tulong)
                     (Etempvar _now tulong) tulong) tlong)
                 (Econst_int (Int.repr 0) tint) tint)
    (Sset _t'1 (Ecast (Etempvar _now tulong) tulong))
    (Sset _t'1 (Ecast (Etempvar _last tulong) tulong)))
  (Sreturn (Some (Etempvar _t'1 tulong))))
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
              (_pb, (Tstruct _wg_peer noattr)) ::
              (_pa, (Tstruct _wg_peer noattr)) ::
              (_ia, (Tstruct _m_identity noattr)) ::
              (_ib, (Tstruct _m_identity noattr)) ::
              (_raw_a, (tarray tuchar 32)) :: (_raw_b, (tarray tuchar 32)) ::
              (_psk, (tarray tuchar 32)) :: (_ssa, (tarray tuchar 32)) ::
              (_ssb, (tarray tuchar 32)) :: (_tmp, (tarray tuchar 32)) ::
              (_ts, (tarray tuchar 12)) :: (_img, (tarray tuchar 148)) ::
              (_img_before, (tarray tuchar 148)) ::
              (_rimg, (tarray tuchar 92)) ::
              (_rimg_before, (tarray tuchar 92)) ::
              (_mi, (Tstruct _m_initiation noattr)) ::
              (_ci, (Tstruct _m_consumed_initiation noattr)) ::
              (_mr, (Tstruct _m_response noattr)) ::
              (_st2, (Tstruct _m_state noattr)) ::
              (_snap, (Tstruct _hs_snap noattr)) ::
              (_d1, (tarray tuchar 32)) :: (_d2, (tarray tuchar 32)) ::
              (_d1__1, (tarray tuchar 32)) :: (_d2__1, (tarray tuchar 32)) ::
              (_first, (tarray tuchar 32)) ::
              (_second, (tarray tuchar 32)) :: nil);
  fn_temps := ((_m1, (tptr (Tstruct _message_handshake_initiation noattr))) ::
               (_m2, (tptr (Tstruct _message_handshake_response noattr))) ::
               (_ret, (tptr (Tstruct _wg_peer noattr))) ::
               (_ka, (tptr (Tstruct _noise_keypair noattr))) ::
               (_kb, (tptr (Tstruct _noise_keypair noattr))) ::
               (_use_psk, tint) :: (_ok1, tint) :: (_acc1, tint) ::
               (_ok2, tint) :: (_acc2, tint) :: (_all_ok, tint) ::
               (_now_b, tulong) :: (_now_a, tulong) :: (_id_a, tulong) ::
               (_allocs0, tulong) :: (_frees0, tulong) ::
               (_fails0, tulong) :: (_mok, tint) :: (_agree, tint) ::
               (_mok__1, tint) :: (_agree__1, tint) :: (_ra, tbool) ::
               (_rb, tbool) :: (_f0, tulong) :: (_t'205, tint) ::
               (_t'204, tint) :: (_t'203, tint) :: (_t'202, tint) ::
               (_t'201, tint) :: (_t'200, tint) :: (_t'199, tint) ::
               (_t'198, tint) :: (_t'197, tint) :: (_t'196, tint) ::
               (_t'195, tulong) :: (_t'194, tint) :: (_t'193, tint) ::
               (_t'192, tint) :: (_t'191, tint) :: (_t'190, tint) ::
               (_t'189, tint) :: (_t'188, tint) :: (_t'187, tint) ::
               (_t'186, tint) :: (_t'185, tint) :: (_t'184, tint) ::
               (_t'183, tint) :: (_t'182, tint) :: (_t'181, tint) ::
               (_t'180, tint) :: (_t'179, tint) :: (_t'178, tbool) ::
               (_t'177, tint) :: (_t'176, tint) :: (_t'175, tulong) ::
               (_t'174, tint) :: (_t'173, tint) :: (_t'172, tint) ::
               (_t'171, tint) :: (_t'170, tint) :: (_t'169, tint) ::
               (_t'168, tint) :: (_t'167, tint) :: (_t'166, tint) ::
               (_t'165, tint) :: (_t'164, tint) :: (_t'163, tint) ::
               (_t'162, tint) :: (_t'161, tint) :: (_t'160, tint) ::
               (_t'159, tint) :: (_t'158, tint) :: (_t'157, tbool) ::
               (_t'156, tint) :: (_t'155, tint) :: (_t'154, tint) ::
               (_t'153, tint) :: (_t'152, tint) :: (_t'151, tint) ::
               (_t'150, tint) :: (_t'149, tint) :: (_t'148, tint) ::
               (_t'147, tint) :: (_t'146, tint) :: (_t'145, tint) ::
               (_t'144, tint) :: (_t'143, tint) :: (_t'142, tint) ::
               (_t'141, tint) :: (_t'140, tint) :: (_t'139, tint) ::
               (_t'138, tint) :: (_t'137, tint) :: (_t'136, tint) ::
               (_t'135, tint) :: (_t'134, tint) ::
               (_t'133, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'132, tulong) :: (_t'131, tint) :: (_t'130, tint) ::
               (_t'129, tint) :: (_t'128, tint) :: (_t'127, tint) ::
               (_t'126, tint) :: (_t'125, tint) :: (_t'124, tint) ::
               (_t'123, tint) :: (_t'122, tint) :: (_t'121, tint) ::
               (_t'120, tint) :: (_t'119, tint) :: (_t'118, tint) ::
               (_t'117, tulong) :: (_t'116, tint) :: (_t'115, tint) ::
               (_t'114, tint) :: (_t'113, tint) :: (_t'112, tint) ::
               (_t'111, tint) :: (_t'110, tint) :: (_t'109, tint) ::
               (_t'108, tint) :: (_t'107, tint) :: (_t'106, tint) ::
               (_t'105, tint) :: (_t'104, tint) :: (_t'103, tint) ::
               (_t'102, tint) :: (_t'101, tint) :: (_t'100, tint) ::
               (_t'99, tint) :: (_t'98, tint) :: (_t'97, tbool) ::
               (_t'96, tint) :: (_t'95, tint) :: (_t'94, tint) ::
               (_t'93, tint) :: (_t'92, tint) :: (_t'91, tint) ::
               (_t'90, tint) :: (_t'89, tint) :: (_t'88, tint) ::
               (_t'87, tint) :: (_t'86, tint) :: (_t'85, tint) ::
               (_t'84, tulong) :: (_t'83, tint) :: (_t'82, tint) ::
               (_t'81, tint) :: (_t'80, tint) :: (_t'79, tint) ::
               (_t'78, tint) :: (_t'77, tint) :: (_t'76, tint) ::
               (_t'75, tint) :: (_t'74, tint) :: (_t'73, tint) ::
               (_t'72, tint) :: (_t'71, tint) :: (_t'70, tint) ::
               (_t'69, tint) :: (_t'68, tint) :: (_t'67, tint) ::
               (_t'66, tint) :: (_t'65, tint) :: (_t'64, tint) ::
               (_t'63, tint) :: (_t'62, tint) :: (_t'61, tint) ::
               (_t'60, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'59, tulong) :: (_t'58, tint) :: (_t'57, tint) ::
               (_t'56, tint) :: (_t'55, tint) :: (_t'54, tint) ::
               (_t'53, tint) :: (_t'52, tint) :: (_t'51, tint) ::
               (_t'50, tint) :: (_t'49, tint) :: (_t'48, tint) ::
               (_t'47, tint) :: (_t'46, tint) :: (_t'45, tint) ::
               (_t'44, tint) :: (_t'43, tint) :: (_t'42, tint) ::
               (_t'41, tint) :: (_t'40, tint) :: (_t'39, tint) ::
               (_t'38, tint) :: (_t'37, tint) :: (_t'36, tint) ::
               (_t'35, tulong) :: (_t'34, tint) :: (_t'33, tint) ::
               (_t'32, tint) :: (_t'31, tint) :: (_t'30, tint) ::
               (_t'29, tint) :: (_t'28, tint) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tint) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tbool) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, (tptr tvoid)) ::
               (_t'18, (tptr tvoid)) :: (_t'17, tint) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, (tptr tvoid)) :: (_t'8, (tptr tvoid)) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tuchar) ::
               (_t'1, tulong) :: (_t'315, tint) :: (_t'314, tbool) ::
               (_t'313, tint) :: (_t'312, tbool) :: (_t'311, tint) ::
               (_t'310, tint) :: (_t'309, tint) :: (_t'308, tint) ::
               (_t'307, tlong) :: (_t'306, tlong) :: (_t'305, tint) ::
               (_t'304, tint) :: (_t'303, tuint) :: (_t'302, tuint) ::
               (_t'301, tuint) :: (_t'300, tuint) :: (_t'299, tuint) ::
               (_t'298, tuint) ::
               (_t'297, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'296, tint) :: (_t'295, tint) :: (_t'294, tuint) ::
               (_t'293, tuint) :: (_t'292, tulong) :: (_t'291, tulong) ::
               (_t'290, tbool) :: (_t'289, tint) :: (_t'288, tulong) ::
               (_t'287, tuint) :: (_t'286, tuint) :: (_t'285, tint) ::
               (_t'284, tuint) :: (_t'283, tuint) :: (_t'282, tulong) ::
               (_t'281, tulong) :: (_t'280, tbool) :: (_t'279, tbool) ::
               (_t'278, tuint) :: (_t'277, tuint) :: (_t'276, tuint) ::
               (_t'275, tuint) :: (_t'274, tuint) :: (_t'273, tuint) ::
               (_t'272, tuint) :: (_t'271, tuint) :: (_t'270, tuint) ::
               (_t'269, tuint) :: (_t'268, tint) :: (_t'267, tuint) ::
               (_t'266, tuint) :: (_t'265, tulong) :: (_t'264, tulong) ::
               (_t'263, tuint) :: (_t'262, tuint) :: (_t'261, tint) ::
               (_t'260, tuint) :: (_t'259, tuint) :: (_t'258, tint) ::
               (_t'257, tuint) :: (_t'256, tuint) :: (_t'255, tulong) ::
               (_t'254, tulong) :: (_t'253, tuint) :: (_t'252, tuint) ::
               (_t'251, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'250, tulong) ::
               (_t'249, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'248, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'247, tuint) :: (_t'246, tuint) :: (_t'245, tbool) ::
               (_t'244, tbool) :: (_t'243, tbool) :: (_t'242, tulong) ::
               (_t'241, tulong) :: (_t'240, tulong) :: (_t'239, tlong) ::
               (_t'238, tint) :: (_t'237, tuint) ::
               (_t'236, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'235, tuint) :: (_t'234, tuint) :: (_t'233, tbool) ::
               (_t'232, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'231, tulong) ::
               (_t'230, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'229, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'228, tuint) :: (_t'227, tuint) :: (_t'226, tbool) ::
               (_t'225, tbool) :: (_t'224, tbool) :: (_t'223, tulong) ::
               (_t'222, tulong) :: (_t'221, tint) :: (_t'220, tuint) ::
               (_t'219, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'218, tuint) :: (_t'217, tuint) :: (_t'216, tbool) ::
               (_t'215, tulong) ::
               (_t'214, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'213, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'212, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'211, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'210, tulong) :: (_t'209, tulong) :: (_t'208, tulong) ::
               (_t'207, tuint) :: (_t'206, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _draw_boottime (Tfunction nil tulong cc_default)) nil)
      (Sassign (Evar _wg_shim_boottime_ns tulong) (Etempvar _t'1 tulong)))
    (Ssequence
      (Sassign (Evar _wg_shim_ratelimit_allow tbool)
        (Econst_int (Int.repr 1) tint))
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
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Evar _raw_b (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
                (Sset _use_psk
                  (Ebinop Oand (Etempvar _t'2 tuchar)
                    (Econst_int (Int.repr 1) tint) tint)))
              (Ssequence
                (Sifthenelse (Etempvar _use_psk tint)
                  (Scall None
                    (Evar _nondet_bytes (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                    ((Evar _psk (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Scall None
                    (Evar _bytes_set (Tfunction
                                       ((tptr tuchar) :: tuchar :: tulong ::
                                        nil) tvoid cc_default))
                    ((Evar _psk (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 0) tint) ::
                     (Econst_int (Int.repr 32) tint) :: nil)))
                (Ssequence
                  (Sset _allocs0 (Evar _wg_shim_allocs tulong))
                  (Ssequence
                    (Sset _frees0 (Evar _wg_shim_frees tulong))
                    (Ssequence
                      (Sset _fails0 (Evar _wg_shim_alloc_failures tulong))
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
                           (Eaddrof
                             (Evar _ita (Tstruct _index_hashtable noattr))
                             (tptr (Tstruct _index_hashtable noattr))) ::
                           (Eaddrof
                             (Evar _pta (Tstruct _pubkey_hashtable noattr))
                             (tptr (Tstruct _pubkey_hashtable noattr))) ::
                           (Evar _raw_a (tarray tuchar 32)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _setup_device (Tfunction
                                                  ((tptr (Tstruct _wg_device noattr)) ::
                                                   (tptr (Tstruct _index_hashtable noattr)) ::
                                                   (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                                   (tptr tuchar) :: nil)
                                                  tvoid cc_default))
                            ((Eaddrof (Evar _wb (Tstruct _wg_device noattr))
                               (tptr (Tstruct _wg_device noattr))) ::
                             (Eaddrof
                               (Evar _itb (Tstruct _index_hashtable noattr))
                               (tptr (Tstruct _index_hashtable noattr))) ::
                             (Eaddrof
                               (Evar _ptb (Tstruct _pubkey_hashtable noattr))
                               (tptr (Tstruct _pubkey_hashtable noattr))) ::
                             (Evar _raw_b (tarray tuchar 32)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _m_identity_of (Tfunction
                                                     ((tptr (Tstruct _m_identity noattr)) ::
                                                      (tptr tuchar) :: nil)
                                                     tvoid cc_default))
                              ((Eaddrof
                                 (Evar _ia (Tstruct _m_identity noattr))
                                 (tptr (Tstruct _m_identity noattr))) ::
                               (Evar _raw_a (tarray tuchar 32)) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _m_identity_of (Tfunction
                                                       ((tptr (Tstruct _m_identity noattr)) ::
                                                        (tptr tuchar) :: nil)
                                                       tvoid cc_default))
                                ((Eaddrof
                                   (Evar _ib (Tstruct _m_identity noattr))
                                   (tptr (Tstruct _m_identity noattr))) ::
                                 (Evar _raw_b (tarray tuchar 32)) :: nil))
                              (Ssequence
                                (Sloop
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'312
                                        (Efield
                                          (Efield
                                            (Evar _wa (Tstruct _wg_device noattr))
                                            _static_identity
                                            (Tstruct _noise_static_identity noattr))
                                          _has_identity tbool))
                                      (Ssequence
                                        (Sset _t'313
                                          (Efield
                                            (Evar _ia (Tstruct _m_identity noattr))
                                            _ok tint))
                                        (Sifthenelse (Ebinop Oeq
                                                       (Etempvar _t'312 tbool)
                                                       (Etempvar _t'313 tint)
                                                       tint)
                                          (Ssequence
                                            (Sset _t'314
                                              (Efield
                                                (Efield
                                                  (Evar _wb (Tstruct _wg_device noattr))
                                                  _static_identity
                                                  (Tstruct _noise_static_identity noattr))
                                                _has_identity tbool))
                                            (Ssequence
                                              (Sset _t'315
                                                (Efield
                                                  (Evar _ib (Tstruct _m_identity noattr))
                                                  _ok tint))
                                              (Sset _t'3
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _t'314 tbool)
                                                    (Etempvar _t'315 tint)
                                                    tint) tbool))))
                                          (Sset _t'3
                                            (Econst_int (Int.repr 0) tint)))))
                                    (Sifthenelse (Eunop Onotbool
                                                   (Etempvar _t'3 tint) tint)
                                      (Scall None
                                        (Evar _check_failed (Tfunction nil
                                                              tvoid
                                                              cc_default))
                                        nil)
                                      Sskip))
                                  Sbreak)
                                (Ssequence
                                  (Sloop
                                    (Ssequence
                                      (Scall (Some _t'4)
                                        (Evar _bytes_eq (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           tulong :: nil)
                                                          tint cc_default))
                                        ((Efield
                                           (Efield
                                             (Evar _wa (Tstruct _wg_device noattr))
                                             _static_identity
                                             (Tstruct _noise_static_identity noattr))
                                           _static_private
                                           (tarray tuchar 32)) ::
                                         (Efield
                                           (Evar _ia (Tstruct _m_identity noattr))
                                           _priv (tarray tuchar 32)) ::
                                         (Econst_int (Int.repr 32) tint) ::
                                         nil))
                                      (Sifthenelse (Eunop Onotbool
                                                     (Etempvar _t'4 tint)
                                                     tint)
                                        (Scall None
                                          (Evar _check_failed (Tfunction nil
                                                                tvoid
                                                                cc_default))
                                          nil)
                                        Sskip))
                                    Sbreak)
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Scall (Some _t'5)
                                          (Evar _bytes_eq (Tfunction
                                                            ((tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             tulong :: nil)
                                                            tint cc_default))
                                          ((Efield
                                             (Efield
                                               (Evar _wb (Tstruct _wg_device noattr))
                                               _static_identity
                                               (Tstruct _noise_static_identity noattr))
                                             _static_private
                                             (tarray tuchar 32)) ::
                                           (Efield
                                             (Evar _ib (Tstruct _m_identity noattr))
                                             _priv (tarray tuchar 32)) ::
                                           (Econst_int (Int.repr 32) tint) ::
                                           nil))
                                        (Sifthenelse (Eunop Onotbool
                                                       (Etempvar _t'5 tint)
                                                       tint)
                                          (Scall None
                                            (Evar _check_failed (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                            nil)
                                          Sskip))
                                      Sbreak)
                                    (Ssequence
                                      (Scall None
                                        (Evar _m_static_public_field 
                                        (Tfunction
                                          ((tptr tuchar) ::
                                           (tptr (Tstruct _m_identity noattr)) ::
                                           (tptr tuchar) :: nil) tvoid
                                          cc_default))
                                        ((Evar _tmp (tarray tuchar 32)) ::
                                         (Eaddrof
                                           (Evar _ia (Tstruct _m_identity noattr))
                                           (tptr (Tstruct _m_identity noattr))) ::
                                         (Evar _raw_a (tarray tuchar 32)) ::
                                         nil))
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Scall (Some _t'6)
                                              (Evar _bytes_eq (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tint
                                                                cc_default))
                                              ((Efield
                                                 (Efield
                                                   (Evar _wa (Tstruct _wg_device noattr))
                                                   _static_identity
                                                   (Tstruct _noise_static_identity noattr))
                                                 _static_public
                                                 (tarray tuchar 32)) ::
                                               (Evar _tmp (tarray tuchar 32)) ::
                                               (Econst_int (Int.repr 32) tint) ::
                                               nil))
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _t'6 tint)
                                                           tint)
                                              (Scall None
                                                (Evar _check_failed (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                nil)
                                              Sskip))
                                          Sbreak)
                                        (Ssequence
                                          (Scall None
                                            (Evar _m_static_public_field 
                                            (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr (Tstruct _m_identity noattr)) ::
                                               (tptr tuchar) :: nil) tvoid
                                              cc_default))
                                            ((Evar _tmp (tarray tuchar 32)) ::
                                             (Eaddrof
                                               (Evar _ib (Tstruct _m_identity noattr))
                                               (tptr (Tstruct _m_identity noattr))) ::
                                             (Evar _raw_b (tarray tuchar 32)) ::
                                             nil))
                                          (Ssequence
                                            (Sloop
                                              (Ssequence
                                                (Scall (Some _t'7)
                                                  (Evar _bytes_eq (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                  ((Efield
                                                     (Efield
                                                       (Evar _wb (Tstruct _wg_device noattr))
                                                       _static_identity
                                                       (Tstruct _noise_static_identity noattr))
                                                     _static_public
                                                     (tarray tuchar 32)) ::
                                                   (Evar _tmp (tarray tuchar 32)) ::
                                                   (Econst_int (Int.repr 32) tint) ::
                                                   nil))
                                                (Sifthenelse (Eunop Onotbool
                                                               (Etempvar _t'7 tint)
                                                               tint)
                                                  (Scall None
                                                    (Evar _check_failed 
                                                    (Tfunction nil tvoid
                                                      cc_default)) nil)
                                                  Sskip))
                                              Sbreak)
                                            (Ssequence
                                              (Ssequence
                                                (Sifthenelse (Etempvar _use_psk tint)
                                                  (Sset _t'8
                                                    (Ecast
                                                      (Evar _psk (tarray tuchar 32))
                                                      (tptr tvoid)))
                                                  (Sset _t'8
                                                    (Ecast
                                                      (Ecast
                                                        (Econst_int (Int.repr 0) tint)
                                                        (tptr tvoid))
                                                      (tptr tvoid))))
                                                (Scall None
                                                  (Evar _setup_peer (Tfunction
                                                                    ((tptr (Tstruct _wg_peer noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                  ((Eaddrof
                                                     (Evar _pb (Tstruct _wg_peer noattr))
                                                     (tptr (Tstruct _wg_peer noattr))) ::
                                                   (Eaddrof
                                                     (Evar _wa (Tstruct _wg_device noattr))
                                                     (tptr (Tstruct _wg_device noattr))) ::
                                                   (Efield
                                                     (Evar _ib (Tstruct _m_identity noattr))
                                                     _pub (tarray tuchar 32)) ::
                                                   (Etempvar _t'8 (tptr tvoid)) ::
                                                   (Econst_int (Int.repr 1) tint) ::
                                                   nil)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sifthenelse (Etempvar _use_psk tint)
                                                    (Sset _t'9
                                                      (Ecast
                                                        (Evar _psk (tarray tuchar 32))
                                                        (tptr tvoid)))
                                                    (Sset _t'9
                                                      (Ecast
                                                        (Ecast
                                                          (Econst_int (Int.repr 0) tint)
                                                          (tptr tvoid))
                                                        (tptr tvoid))))
                                                  (Scall None
                                                    (Evar _setup_peer 
                                                    (Tfunction
                                                      ((tptr (Tstruct _wg_peer noattr)) ::
                                                       (tptr (Tstruct _wg_device noattr)) ::
                                                       (tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tvoid
                                                      cc_default))
                                                    ((Eaddrof
                                                       (Evar _pa (Tstruct _wg_peer noattr))
                                                       (tptr (Tstruct _wg_peer noattr))) ::
                                                     (Eaddrof
                                                       (Evar _wb (Tstruct _wg_device noattr))
                                                       (tptr (Tstruct _wg_device noattr))) ::
                                                     (Efield
                                                       (Evar _ia (Tstruct _m_identity noattr))
                                                       _pub
                                                       (tarray tuchar 32)) ::
                                                     (Etempvar _t'9 (tptr tvoid)) ::
                                                     (Econst_int (Int.repr 2) tint) ::
                                                     nil)))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _m_precomputed 
                                                    (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr (Tstruct _m_identity noattr)) ::
                                                       (tptr tuchar) :: nil)
                                                      tvoid cc_default))
                                                    ((Evar _ssa (tarray tuchar 32)) ::
                                                     (Eaddrof
                                                       (Evar _ia (Tstruct _m_identity noattr))
                                                       (tptr (Tstruct _m_identity noattr))) ::
                                                     (Efield
                                                       (Evar _ib (Tstruct _m_identity noattr))
                                                       _pub
                                                       (tarray tuchar 32)) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _m_precomputed 
                                                      (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr (Tstruct _m_identity noattr)) ::
                                                         (tptr tuchar) ::
                                                         nil) tvoid
                                                        cc_default))
                                                      ((Evar _ssb (tarray tuchar 32)) ::
                                                       (Eaddrof
                                                         (Evar _ib (Tstruct _m_identity noattr))
                                                         (tptr (Tstruct _m_identity noattr))) ::
                                                       (Efield
                                                         (Evar _ia (Tstruct _m_identity noattr))
                                                         _pub
                                                         (tarray tuchar 32)) ::
                                                       nil))
                                                    (Ssequence
                                                      (Sloop
                                                        (Ssequence
                                                          (Scall (Some _t'10)
                                                            (Evar _bytes_eq 
                                                            (Tfunction
                                                              ((tptr tuchar) ::
                                                               (tptr tuchar) ::
                                                               tulong :: nil)
                                                              tint
                                                              cc_default))
                                                            ((Efield
                                                               (Efield
                                                                 (Evar _pb (Tstruct _wg_peer noattr))
                                                                 _handshake
                                                                 (Tstruct _noise_handshake noattr))
                                                               _precomputed_static_static
                                                               (tarray tuchar 32)) ::
                                                             (Evar _ssa (tarray tuchar 32)) ::
                                                             (Econst_int (Int.repr 32) tint) ::
                                                             nil))
                                                          (Sifthenelse 
                                                            (Eunop Onotbool
                                                              (Etempvar _t'10 tint)
                                                              tint)
                                                            (Scall None
                                                              (Evar _check_failed 
                                                              (Tfunction nil
                                                                tvoid
                                                                cc_default))
                                                              nil)
                                                            Sskip))
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sloop
                                                          (Ssequence
                                                            (Scall (Some _t'11)
                                                              (Evar _bytes_eq 
                                                              (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 tulong ::
                                                                 nil) tint
                                                                cc_default))
                                                              ((Efield
                                                                 (Efield
                                                                   (Evar _pa (Tstruct _wg_peer noattr))
                                                                   _handshake
                                                                   (Tstruct _noise_handshake noattr))
                                                                 _precomputed_static_static
                                                                 (tarray tuchar 32)) ::
                                                               (Evar _ssb (tarray tuchar 32)) ::
                                                               (Econst_int (Int.repr 32) tint) ::
                                                               nil))
                                                            (Sifthenelse 
                                                              (Eunop Onotbool
                                                                (Etempvar _t'11 tint)
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
                                                                (Scall (Some _t'12)
                                                                  (Evar _bytes_eq 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                  ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _preshared_key
                                                                    (tarray tuchar 32)) ::
                                                                   (Evar _psk (tarray tuchar 32)) ::
                                                                   (Econst_int (Int.repr 32) tint) ::
                                                                   nil))
                                                                (Sifthenelse (Etempvar _t'12 tint)
                                                                  (Ssequence
                                                                    (Scall (Some _t'14)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _preshared_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _psk (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'13
                                                                    (Ecast
                                                                    (Etempvar _t'14 tint)
                                                                    tbool)))
                                                                  (Sset _t'13
                                                                    (Econst_int (Int.repr 0) tint))))
                                                              (Sifthenelse 
                                                                (Eunop Onotbool
                                                                  (Etempvar _t'13 tint)
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
                                                              (Evar _m_label_key 
                                                              (Tfunction
                                                                ((tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 (tptr tuchar) ::
                                                                 nil) tvoid
                                                                cc_default))
                                                              ((Evar _tmp (tarray tuchar 32)) ::
                                                               (Evar _x_handshake__M_LABEL_MAC1 (tarray tuchar 8)) ::
                                                               (Efield
                                                                 (Evar _ib (Tstruct _m_identity noattr))
                                                                 _pub
                                                                 (tarray tuchar 32)) ::
                                                               nil))
                                                            (Ssequence
                                                              (Sloop
                                                                (Ssequence
                                                                  (Scall (Some _t'15)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _message_mac1_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _tmp (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                  (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'15 tint)
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
                                                                  (Evar _m_label_key 
                                                                  (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Evar _tmp (tarray tuchar 32)) ::
                                                                   (Evar _x_handshake__M_LABEL_COOKIE (tarray tuchar 8)) ::
                                                                   (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                   nil))
                                                                (Ssequence
                                                                  (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'16)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _cookie_decryption_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _tmp (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'16 tint)
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
                                                                    (Sset _t'310
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'310 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'311
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sset _t'17
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'311 tint)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'17
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'17 tint)
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
                                                                    (Scall (Some _t'18)
                                                                    (Evar _quickproof_malloc 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                                                    nil))
                                                                    (Sset _m1
                                                                    (Etempvar _t'18 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'19)
                                                                    (Evar _quickproof_malloc 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Esizeof (Tstruct _message_handshake_response noattr) tulong) ::
                                                                    nil))
                                                                    (Sset _m2
                                                                    (Etempvar _t'19 (tptr tvoid))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Sset _t'20
                                                                    (Econst_int (Int.repr 1) tint))
                                                                    (Sset _t'20
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sifthenelse (Etempvar _t'20 tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'308
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'308 tint)
                                                                    (Ssequence
                                                                    (Sset _t'309
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Etempvar _t'309 tint)
                                                                    tbool)))
                                                                    (Sset _t'21
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _all_ok
                                                                    (Etempvar _t'21 tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _fill_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _init_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img_before (tarray tuchar 148)) ::
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _draw_real_clock 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'306
                                                                    (Evar _wg_shim_real_sec tlong))
                                                                    (Ssequence
                                                                    (Sset _t'307
                                                                    (Evar _wg_shim_real_nsec tlong))
                                                                    (Scall None
                                                                    (Evar _m_tai64n 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tlong ::
                                                                    tlong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _ts (tarray tuchar 12)) ::
                                                                    (Etempvar _t'306 tlong) ::
                                                                    (Etempvar _t'307 tlong) ::
                                                                    nil))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
                                                                    (Evar _wg_noise_handshake_create_initiation 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _ok1
                                                                    (Etempvar _t'22 tbool)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'305
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'305 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ok1 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _t'24 tint)
                                                                    tbool)))
                                                                    (Sset _t'23
                                                                    (Econst_int (Int.repr 0) tint)))
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
                                                                    (Evar _init_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 148)) ::
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
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
                                                                    ((Evar _img (tarray tuchar 148)) ::
                                                                    (Evar _img_before (tarray tuchar 148)) ::
                                                                    (Econst_int (Int.repr 148) tint) ::
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
                                                                    Sbreak)))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'304
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'304 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _m_create_initiation 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _m_initiation noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    (tptr (Tstruct _m_initiation noattr))) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    _static_identity
                                                                    (Tstruct _noise_static_identity noattr))
                                                                    _static_public
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _ssa (tarray tuchar 32)) ::
                                                                    (Evar _wg_shim_random_log (tarray tuchar 32)) ::
                                                                    (Evar _ts (tarray tuchar 12)) ::
                                                                    nil))
                                                                    (Sset _mok
                                                                    (Etempvar _t'26 tint)))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ok1 tint)
                                                                    (Etempvar _mok tint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Etempvar _mok tint)
                                                                    tbool))
                                                                    (Sset _t'27
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'27 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'29)
                                                                    (Evar _bytes_zero 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _ts (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sset _t'28
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'29 tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'28
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _all_ok
                                                                    (Etempvar _t'28 tint)))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ok1 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _init_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 148)) ::
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'303
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _header
                                                                    (Tstruct _message_header noattr))
                                                                    _type
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'303 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
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
                                                                    (Sset _t'299
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'300
                                                                    (Evar _wg_shim_random_u32 tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'299 tuint)
                                                                    (Etempvar _t'300 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'301
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'302
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sset _t'30
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'301 tuint)
                                                                    (Etempvar _t'302 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'30
                                                                    (Econst_int (Int.repr 0) tint)))))
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
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'31)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'31 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'298
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Scall (Some _t'33)
                                                                    (Evar _table_index_unique 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Etempvar _t'298 tuint) ::
                                                                    nil)))
                                                                    (Sset _t'32
                                                                    (Ecast
                                                                    (Etempvar _t'33 tint)
                                                                    tbool)))
                                                                    (Sset _t'32
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'32 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'35)
                                                                    (Evar _table_len 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    nil))
                                                                    (Sset _t'34
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'35 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'34
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'34 tint)
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
                                                                    (Sset _t'296
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _type
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'296 tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'297
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _peer
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sset _t'36
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'297 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Eaddrof
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'36
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'36 tint)
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
                                                                    (Scall (Some _t'37)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'37 tint)
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
                                                                    (Scall (Some _t'38)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_static
                                                                    (tarray tuchar 48)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _enc_static
                                                                    (tarray tuchar 48)) ::
                                                                    (Econst_int (Int.repr 48) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'38 tint)
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
                                                                    (Scall (Some _t'39)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_timestamp
                                                                    (tarray tuchar 28)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _enc_timestamp
                                                                    (tarray tuchar 28)) ::
                                                                    (Econst_int (Int.repr 28) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'39 tint)
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
                                                                    (Scall (Some _t'40)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _img (tarray tuchar 148))
                                                                    (Econst_int (Int.repr 116) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Evar _img_before (tarray tuchar 148))
                                                                    (Econst_int (Int.repr 116) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'40 tint)
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
                                                                    (Sset _t'295
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'295 tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
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
                                                                    (Scall (Some _t'41)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _hash
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'41 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'43)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _chaining_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'42
                                                                    (Ecast
                                                                    (Etempvar _t'43 tint)
                                                                    tbool)))
                                                                    (Sset _t'42
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'42 tint)
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
                                                                    (Scall (Some _t'44)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'44 tint)
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
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'45)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'45 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'47)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sset _t'46
                                                                    (Ecast
                                                                    (Etempvar _t'47 tint)
                                                                    tbool)))
                                                                    (Sset _t'46
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'46 tint)
                                                                    (Ssequence
                                                                    (Sset _t'293
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'294
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Sset _t'48
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'293 tuint)
                                                                    (Etempvar _t'294 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'48
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'48 tint)
                                                                    (Ssequence
                                                                    (Sset _t'291
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'292
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Sset _t'49
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'291 tulong)
                                                                    (Etempvar _t'292 tulong)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'49
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'49 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'51)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _remote_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'50
                                                                    (Ecast
                                                                    (Etempvar _t'51 tint)
                                                                    tbool)))
                                                                    (Sset _t'50
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'50 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'53)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _precomputed_static_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _precomputed_static_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'52
                                                                    (Ecast
                                                                    (Etempvar _t'53 tint)
                                                                    tbool)))
                                                                    (Sset _t'52
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'52 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'55)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _preshared_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _preshared_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'54
                                                                    (Ecast
                                                                    (Etempvar _t'55 tint)
                                                                    tbool)))
                                                                    (Sset _t'54
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'54 tint)
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
                                                                    (Evar _wg_cookie_add_mac_to_packet 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_label_key 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _tmp (tarray tuchar 32)) ::
                                                                    (Evar _x_handshake__M_LABEL_MAC1 (tarray tuchar 8)) ::
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_mac 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _img (tarray tuchar 148))
                                                                    (Econst_int (Int.repr 116) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Evar _tmp (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    (Evar _img (tarray tuchar 148)) ::
                                                                    (Econst_int (Int.repr 116) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bytes_set 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuchar ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _img (tarray tuchar 148))
                                                                    (Econst_int (Int.repr 132) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _init_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img_before (tarray tuchar 148)) ::
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'56)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 148)) ::
                                                                    (Evar _img_before (tarray tuchar 148)) ::
                                                                    (Econst_int (Int.repr 148) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'56 tint)
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
                                                                    (Sset _t'290
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _have_sent_mac1
                                                                    tbool))
                                                                    (Sifthenelse (Etempvar _t'290 tbool)
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
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _latest_cookie
                                                                    (Tstruct _cookie noattr))
                                                                    _last_mac1_sent
                                                                    (tarray tuchar 16)) ::
                                                                    (Ebinop Oadd
                                                                    (Evar _img (tarray tuchar 148))
                                                                    (Econst_int (Int.repr 116) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
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
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'59)
                                                                    (Evar _draw_boottime 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sassign
                                                                    (Evar _wg_shim_boottime_ns tulong)
                                                                    (Etempvar _t'59 tulong)))
                                                                    (Ssequence
                                                                    (Sset _now_b
                                                                    (Evar _wg_shim_boottime_ns tulong))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'60)
                                                                    (Evar _wg_noise_handshake_consume_initiation 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    (tptr (Tstruct _wg_peer noattr))
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Sset _ret
                                                                    (Etempvar _t'60 (tptr (Tstruct _wg_peer noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'289
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'289 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'62)
                                                                    (Evar _m_consume_initiation_1 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _m_consumed_initiation noattr)) ::
                                                                    (tptr (Tstruct _m_identity noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    (tptr (Tstruct _m_consumed_initiation noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    (tptr (Tstruct _m_identity noattr))) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_static
                                                                    (tarray tuchar 48)) ::
                                                                    nil))
                                                                    (Sset _t'61
                                                                    (Ecast
                                                                    (Etempvar _t'62 tint)
                                                                    tbool)))
                                                                    (Sset _t'61
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'61 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'64)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _spub
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'63
                                                                    (Ecast
                                                                    (Etempvar _t'64 tint)
                                                                    tbool)))
                                                                    (Sset _t'63
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'63 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'66)
                                                                    (Evar _m_consume_initiation_2 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _m_consumed_initiation noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    (tptr (Tstruct _m_consumed_initiation noattr))) ::
                                                                    (Evar _ssb (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_timestamp
                                                                    (tarray tuchar 28)) ::
                                                                    nil))
                                                                    (Sset _t'65
                                                                    (Ecast
                                                                    (Etempvar _t'66 tint)
                                                                    tbool)))
                                                                    (Sset _t'65
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'65 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'68)
                                                                    (Evar _m_ts_newer 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _ts
                                                                    (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    nil))
                                                                    (Sset _t'67
                                                                    (Ecast
                                                                    (Etempvar _t'68 tint)
                                                                    tbool)))
                                                                    (Sset _t'67
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'67 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'288
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Scall (Some _t'70)
                                                                    (Evar _m_not_flood 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _t'288 tulong) ::
                                                                    (Etempvar _now_b tulong) ::
                                                                    nil)))
                                                                    (Sset _t'69
                                                                    (Ecast
                                                                    (Etempvar _t'70 tint)
                                                                    tbool)))
                                                                    (Sset _t'69
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _acc1
                                                                    (Etempvar _t'69 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Sset _t'71
                                                                    (Ecast
                                                                    (Ebinop Oge
                                                                    (Etempvar _now_b tulong)
                                                                    (Econst_int (Int.repr 20000000) tint)
                                                                    tint)
                                                                    tbool))
                                                                    (Sset _t'71
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _all_ok
                                                                    (Etempvar _t'71 tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _init_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _img_before (tarray tuchar 148)) ::
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'72)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _img (tarray tuchar 148)) ::
                                                                    (Evar _img_before (tarray tuchar 148)) ::
                                                                    (Econst_int (Int.repr 148) tint) ::
                                                                    nil))
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
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc1 tint)
                                                                    tint)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ret (tptr (Tstruct _wg_peer noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'74)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'73
                                                                    (Ecast
                                                                    (Etempvar _t'74 tint)
                                                                    tbool)))
                                                                    (Sset _t'73
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'73 tint)
                                                                    (Ssequence
                                                                    (Sset _t'287
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'75
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'287 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'75
                                                                    (Econst_int (Int.repr 0) tint))))
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
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ret (tptr (Tstruct _wg_peer noattr)))
                                                                    (Eaddrof
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'286
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'76
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'286 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'76
                                                                    (Econst_int (Int.repr 0) tint)))
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
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _wg_peer_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ret (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'285
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'285 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
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
                                                                    (Scall (Some _t'77)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'77 tint)
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
                                                                    (Scall (Some _t'78)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _ts
                                                                    (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'78 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'80)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _ts
                                                                    (tarray tuchar 12)) ::
                                                                    (Evar _ts (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sset _t'79
                                                                    (Ecast
                                                                    (Etempvar _t'80 tint)
                                                                    tbool)))
                                                                    (Sset _t'79
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'79 tint)
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
                                                                    (Scall (Some _t'81)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _hash
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'81 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'83)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _chaining_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'82
                                                                    (Ecast
                                                                    (Etempvar _t'83 tint)
                                                                    tbool)))
                                                                    (Sset _t'82
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'82 tint)
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
                                                                    (Sset _t'283
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'284
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'283 tuint)
                                                                    (Etempvar _t'284 tuint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'282
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Scall (Some _t'84)
                                                                    (Evar _m_last_consumption 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _t'282 tulong) ::
                                                                    (Etempvar _now_b tulong) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Sset _t'281
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'281 tulong)
                                                                    (Etempvar _t'84 tulong)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)))
                                                                    Sbreak)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'85)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'85 tint)
                                                                    (Ssequence
                                                                    (Sset _t'279
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _hashed
                                                                    tbool))
                                                                    (Ssequence
                                                                    (Sset _t'280
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _hashed
                                                                    tbool))
                                                                    (Sset _t'86
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'279 tbool)
                                                                    (Etempvar _t'280 tbool)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'86
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'86 tint)
                                                                    (Ssequence
                                                                    (Sset _t'277
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'278
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sset _t'87
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'277 tuint)
                                                                    (Etempvar _t'278 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'87
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'87 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak))))))))))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'88)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'88 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'90)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d2 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _t'89
                                                                    (Ecast
                                                                    (Etempvar _t'90 tint)
                                                                    tbool)))
                                                                    (Sset _t'89
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'89 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'92)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1 (tarray tuchar 32)) ::
                                                                    (Evar _d2 (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'91
                                                                    (Ecast
                                                                    (Etempvar _t'92 tint)
                                                                    tbool)))
                                                                    (Sset _t'91
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _agree
                                                                    (Etempvar _t'91 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _agree tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'94)
                                                                    (Evar _bytes_zero 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _ssa (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'93
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'94 tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'93
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'93 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'96)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _ssa (tarray tuchar 32)) ::
                                                                    (Evar _ssb (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'95
                                                                    (Ecast
                                                                    (Etempvar _t'96 tint)
                                                                    tbool)))
                                                                    (Sset _t'95
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _agree
                                                                    (Etempvar _t'95 tint)))
                                                                    (Ssequence
                                                                    (Sset _all_ok
                                                                    (Etempvar _agree tint))
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc1 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    Sskip))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc1 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _fill_resp 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _resp_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _rimg_before (tarray tuchar 92)) ::
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'97)
                                                                    (Evar _wg_noise_handshake_create_response 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _ok2
                                                                    (Etempvar _t'97 tbool)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'98)
                                                                    (Evar _m_create_response 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _m_response noattr)) ::
                                                                    (tptr (Tstruct _m_state noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    (tptr (Tstruct _m_response noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    (tptr (Tstruct _m_state noattr))) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_static
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _psk (tarray tuchar 32)) ::
                                                                    (Evar _wg_shim_random_log (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _mok__1
                                                                    (Etempvar _t'98 tint)))
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ok2 tint)
                                                                    (Etempvar _mok__1 tint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'99)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1__1 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'99 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'101)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d2__1 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _t'100
                                                                    (Ecast
                                                                    (Etempvar _t'101 tint)
                                                                    tbool)))
                                                                    (Sset _t'100
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'100 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'103)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1__1 (tarray tuchar 32)) ::
                                                                    (Evar _d2__1 (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'102
                                                                    (Ecast
                                                                    (Etempvar _t'103 tint)
                                                                    tbool)))
                                                                    (Sset _t'102
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'102 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'105)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1__1 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _t'104
                                                                    (Ecast
                                                                    (Etempvar _t'105 tint)
                                                                    tbool)))
                                                                    (Sset _t'104
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'104 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'107)
                                                                    (Evar _m_dh 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d2__1 (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Sset _t'106
                                                                    (Ecast
                                                                    (Etempvar _t'107 tint)
                                                                    tbool)))
                                                                    (Sset _t'106
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'106 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'109)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _d1__1 (tarray tuchar 32)) ::
                                                                    (Evar _d2__1 (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'108
                                                                    (Ecast
                                                                    (Etempvar _t'109 tint)
                                                                    tbool)))
                                                                    (Sset _t'108
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _agree__1
                                                                    (Etempvar _t'108 tint)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _agree__1 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'111)
                                                                    (Evar _bytes_zero 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'110
                                                                    (Ecast
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'111 tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'110
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sset _all_ok
                                                                    (Etempvar _t'110 tint)))
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ok2 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    Sskip)))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ok2 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _resp_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _rimg (tarray tuchar 92)) ::
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'276
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _header
                                                                    (Tstruct _message_header noattr))
                                                                    _type
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'276 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
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
                                                                    (Sset _t'274
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _receiver_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'275
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'274 tuint)
                                                                    (Etempvar _t'275 tuint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)))
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'270
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'271
                                                                    (Evar _wg_shim_random_u32 tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'270 tuint)
                                                                    (Etempvar _t'271 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'272
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'273
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sset _t'112
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'272 tuint)
                                                                    (Etempvar _t'273 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'112
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'112 tint)
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
                                                                    (Ssequence
                                                                    (Scall (Some _t'113)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'113 tint)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'269
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Scall (Some _t'115)
                                                                    (Evar _table_index_unique 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    tuint ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Etempvar _t'269 tuint) ::
                                                                    nil)))
                                                                    (Sset _t'114
                                                                    (Ecast
                                                                    (Etempvar _t'115 tint)
                                                                    tbool)))
                                                                    (Sset _t'114
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'114 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'117)
                                                                    (Evar _table_len 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    nil))
                                                                    (Sset _t'116
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'117 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'116
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'116 tint)
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
                                                                    (Scall (Some _t'118)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'118 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'120)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _encrypted_nothing
                                                                    (tarray tuchar 16)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _enc_nothing
                                                                    (tarray tuchar 16)) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))
                                                                    (Sset _t'119
                                                                    (Ecast
                                                                    (Etempvar _t'120 tint)
                                                                    tbool)))
                                                                    (Sset _t'119
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'119 tint)
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
                                                                    (Scall (Some _t'121)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _rimg (tarray tuchar 92))
                                                                    (Econst_int (Int.repr 60) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Ebinop Oadd
                                                                    (Evar _rimg_before (tarray tuchar 92))
                                                                    (Econst_int (Int.repr 60) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'121 tint)
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
                                                                    (Sset _t'268
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'268 tint)
                                                                    (Econst_int (Int.repr 3) tint)
                                                                    tint)
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
                                                                    (Scall (Some _t'122)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _hash
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'122 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'124)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _chaining_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'123
                                                                    (Ecast
                                                                    (Etempvar _t'124 tint)
                                                                    tbool)))
                                                                    (Sset _t'123
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'123 tint)
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
                                                                    (Scall (Some _t'125)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'125 tint)
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
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'126)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'126 tint)
                                                                    (Ssequence
                                                                    (Sset _t'266
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'267
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Sset _t'127
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'266 tuint)
                                                                    (Etempvar _t'267 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'127
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'127 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'129)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sset _t'128
                                                                    (Ecast
                                                                    (Etempvar _t'129 tint)
                                                                    tbool)))
                                                                    (Sset _t'128
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'128 tint)
                                                                    (Ssequence
                                                                    (Sset _t'264
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'265
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Sset _t'130
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'264 tulong)
                                                                    (Etempvar _t'265 tulong)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'130
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'130 tint)
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
                                                                    (Evar _wg_cookie_add_mac_to_packet 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    (Esizeof (Tstruct _message_handshake_response noattr) tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_label_key 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _tmp (tarray tuchar 32)) ::
                                                                    (Evar _x_handshake__M_LABEL_MAC1 (tarray tuchar 8)) ::
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_mac 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _rimg (tarray tuchar 92))
                                                                    (Econst_int (Int.repr 60) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Evar _tmp (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    (Evar _rimg (tarray tuchar 92)) ::
                                                                    (Econst_int (Int.repr 60) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _bytes_set 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    tuchar ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Ebinop Oadd
                                                                    (Evar _rimg (tarray tuchar 92))
                                                                    (Econst_int (Int.repr 76) tint)
                                                                    (tptr tuchar)) ::
                                                                    (Econst_int (Int.repr 0) tint) ::
                                                                    (Econst_int (Int.repr 16) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _resp_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _rimg_before (tarray tuchar 92)) ::
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'131)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _rimg (tarray tuchar 92)) ::
                                                                    (Evar _rimg_before (tarray tuchar 92)) ::
                                                                    (Econst_int (Int.repr 92) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'131 tint)
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
                                                                    (Scall (Some _t'132)
                                                                    (Evar _draw_boottime 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Sassign
                                                                    (Evar _wg_shim_boottime_ns tulong)
                                                                    (Etempvar _t'132 tulong)))
                                                                    (Ssequence
                                                                    (Sset _now_a
                                                                    (Evar _wg_shim_boottime_ns tulong))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'133)
                                                                    (Evar _wg_noise_handshake_consume_response 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    (tptr (Tstruct _wg_peer noattr))
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wa (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Sset _ret
                                                                    (Etempvar _t'133 (tptr (Tstruct _wg_peer noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'261
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'261 tint)
                                                                    (Ssequence
                                                                    (Sset _t'262
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _receiver_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'263
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sset _t'134
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'262 tuint)
                                                                    (Etempvar _t'263 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'134
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'134 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'136)
                                                                    (Evar _m_consume_response 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _m_state noattr)) ::
                                                                    (tptr (Tstruct _m_state noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    (tptr (Tstruct _m_state noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    (tptr (Tstruct _m_state noattr))) ::
                                                                    (Efield
                                                                    (Evar _mi (Tstruct _m_initiation noattr))
                                                                    _eph_priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _priv
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _psk (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _encrypted_nothing
                                                                    (tarray tuchar 16)) ::
                                                                    nil))
                                                                    (Sset _t'135
                                                                    (Ecast
                                                                    (Etempvar _t'136 tint)
                                                                    tbool)))
                                                                    (Sset _t'135
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _acc2
                                                                    (Etempvar _t'135 tint)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _resp_img 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr (Tstruct _message_handshake_response noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _rimg_before (tarray tuchar 92)) ::
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Scall (Some _t'137)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Evar _rimg (tarray tuchar 92)) ::
                                                                    (Evar _rimg_before (tarray tuchar 92)) ::
                                                                    (Econst_int (Int.repr 92) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'137 tint)
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
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc2 tint)
                                                                    tint)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ret (tptr (Tstruct _wg_peer noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'139)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'138
                                                                    (Ecast
                                                                    (Etempvar _t'139 tint)
                                                                    tbool)))
                                                                    (Sset _t'138
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'138 tint)
                                                                    (Ssequence
                                                                    (Sset _t'260
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'140
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'260 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'140
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'140 tint)
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
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _ret (tptr (Tstruct _wg_peer noattr)))
                                                                    (Eaddrof
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'259
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'141
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'259 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'141
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'141 tint)
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
                                                                    (Evar _wg_peer_put 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _ret (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sset _t'258
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _state
                                                                    tint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'258 tint)
                                                                    (Econst_int (Int.repr 4) tint)
                                                                    tint)
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
                                                                    (Scall (Some _t'142)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'142 tint)
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
                                                                    (Scall (Some _t'143)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _hash
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'143 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'145)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _chaining_key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'144
                                                                    (Ecast
                                                                    (Etempvar _t'145 tint)
                                                                    tbool)))
                                                                    (Sset _t'144
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'144 tint)
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
                                                                    (Sset _t'256
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'257
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'256 tuint)
                                                                    (Etempvar _t'257 tuint)
                                                                    tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)))
                                                                    Sbreak)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'146)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _ephemeral_private
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'146 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'148)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _latest_timestamp
                                                                    (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Sset _t'147
                                                                    (Ecast
                                                                    (Etempvar _t'148 tint)
                                                                    tbool)))
                                                                    (Sset _t'147
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'147 tint)
                                                                    (Ssequence
                                                                    (Sset _t'254
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Sset _t'255
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _last_initiation_consumption
                                                                    tulong))
                                                                    (Sset _t'149
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'254 tulong)
                                                                    (Etempvar _t'255 tulong)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'149
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'149 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'151)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    (Sset _t'150
                                                                    (Ecast
                                                                    (Etempvar _t'151 tint)
                                                                    tbool)))
                                                                    (Sset _t'150
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'150 tint)
                                                                    (Ssequence
                                                                    (Sset _t'252
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'253
                                                                    (Efield
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Sset _t'152
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'252 tuint)
                                                                    (Etempvar _t'253 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'152
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'152 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak))))))))
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _all_ok tint)
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse (Etempvar _acc2 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'154)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'153
                                                                    (Ecast
                                                                    (Etempvar _t'154 tint)
                                                                    tbool)))
                                                                    (Sset _t'153
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'153 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'156)
                                                                    (Evar _bytes_eq 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Efield
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _mr (Tstruct _m_response noattr))
                                                                    _st
                                                                    (Tstruct _m_state noattr))
                                                                    _h
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'155
                                                                    (Ecast
                                                                    (Etempvar _t'156 tint)
                                                                    tbool)))
                                                                    (Sset _t'155
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'155 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc2 tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))
                                                                    Sskip)
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _m_transport 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _first (tarray tuchar 32)) ::
                                                                    (Evar _second (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _st2 (Tstruct _m_state noattr))
                                                                    _ck
                                                                    (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _f0
                                                                    (Evar _wg_shim_alloc_failures tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'157)
                                                                    (Evar _wg_noise_handshake_begin_session 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_handshake noattr)) ::
                                                                    (tptr (Tstruct _noise_keypairs noattr)) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    (tptr (Tstruct _noise_keypairs noattr))) ::
                                                                    nil))
                                                                    (Sset _ra
                                                                    (Ecast
                                                                    (Etempvar _t'157 tbool)
                                                                    tbool)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'250
                                                                    (Evar _wg_shim_alloc_failures tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'250 tulong)
                                                                    (Etempvar _f0 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ra tbool)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'159)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'158
                                                                    (Ecast
                                                                    (Etempvar _t'159 tint)
                                                                    tbool)))
                                                                    (Sset _t'158
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'158 tint)
                                                                    (Ssequence
                                                                    (Sset _t'251
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'160
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'251 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'160
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'160 tint)
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
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _ra tbool)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _ka
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'249
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _previous_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'161
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'249 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'161
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'161 tint)
                                                                    (Ssequence
                                                                    (Sset _t'248
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'162
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'248 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'162
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'162 tint)
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
                                                                    (Sset _t'245
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _i_am_the_initiator
                                                                    tbool))
                                                                    (Sifthenelse (Etempvar _t'245 tbool)
                                                                    (Ssequence
                                                                    (Sset _t'246
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'247
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sset _t'163
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'246 tuint)
                                                                    (Etempvar _t'247 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'163
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'163 tint)
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
                                                                    (Scall (Some _t'164)
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
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _first (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'164 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'166)
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
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _second (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'165
                                                                    (Ecast
                                                                    (Etempvar _t'166 tint)
                                                                    tbool)))
                                                                    (Sset _t'165
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'165 tint)
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
                                                                    (Sset _t'243
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _is_valid
                                                                    tbool))
                                                                    (Sifthenelse (Etempvar _t'243 tbool)
                                                                    (Ssequence
                                                                    (Sset _t'244
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _is_valid
                                                                    tbool))
                                                                    (Sset _t'167
                                                                    (Ecast
                                                                    (Etempvar _t'244 tbool)
                                                                    tbool)))
                                                                    (Sset _t'167
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'167 tint)
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
                                                                    (Sset _t'241
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _birthdate
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'241 tulong)
                                                                    (Etempvar _now_a tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'242
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _birthdate
                                                                    tulong))
                                                                    (Sset _t'168
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'242 tulong)
                                                                    (Etempvar _now_a tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'168
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'168 tint)
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
                                                                    (Sset _t'239
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending_counter
                                                                    (Tstruct ___gp_atomic64_t noattr))
                                                                    _counter
                                                                    tlong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'239 tlong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'240
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving_counter
                                                                    (Tstruct _noise_replay_counter noattr))
                                                                    _counter
                                                                    tulong))
                                                                    (Sset _t'169
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'240 tulong)
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'169
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'169 tint)
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
                                                                    (Ssequence
                                                                    (Sset _t'237
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'237 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'238
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _type
                                                                    tint))
                                                                    (Sset _t'170
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'238 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'170
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'170 tint)
                                                                    (Ssequence
                                                                    (Sset _t'236
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _peer
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sset _t'171
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'236 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Eaddrof
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'171
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'171 tint)
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
                                                                    (Ssequence
                                                                    (Sset _t'234
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'235
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'234 tuint)
                                                                    (Etempvar _t'235 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'173)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    (Sset _t'172
                                                                    (Ecast
                                                                    (Etempvar _t'173 tint)
                                                                    tbool)))
                                                                    (Sset _t'172
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                    (Sifthenelse (Etempvar _t'172 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'175)
                                                                    (Evar _table_len 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    nil))
                                                                    (Sset _t'174
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'175 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'174
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'174 tint)
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
                                                                    (Sset _t'233
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _hashed
                                                                    tbool))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'233 tbool)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'177)
                                                                    (Evar _hs_zeroed_from 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'176
                                                                    (Ecast
                                                                    (Etempvar _t'177 tint)
                                                                    tbool)))
                                                                    (Sset _t'176
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'176 tint)
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
                                                                    (Sset _id_a
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _internal_id
                                                                    tulong))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _hs_take 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _f0
                                                                    (Evar _wg_shim_alloc_failures tulong))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'178)
                                                                    (Evar _wg_noise_handshake_begin_session 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_handshake noattr)) ::
                                                                    (tptr (Tstruct _noise_keypairs noattr)) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    (tptr (Tstruct _noise_keypairs noattr))) ::
                                                                    nil))
                                                                    (Sset _rb
                                                                    (Ecast
                                                                    (Etempvar _t'178 tbool)
                                                                    tbool)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'231
                                                                    (Evar _wg_shim_alloc_failures tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _t'231 tulong)
                                                                    (Etempvar _f0 tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _rb tbool)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'180)
                                                                    (Evar _hs_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'179
                                                                    (Ecast
                                                                    (Etempvar _t'180 tint)
                                                                    tbool)))
                                                                    (Sset _t'179
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'179 tint)
                                                                    (Ssequence
                                                                    (Sset _t'232
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'181
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'232 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'181
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'181 tint)
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
                                                                    (Evar _wg_noise_keypairs_clear 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_keypairs noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    (tptr (Tstruct _noise_keypairs noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
                                                                    Sskip))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _rb tbool)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip)
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _kb
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop One
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'230
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _previous_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'182
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'230 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'182
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'182 tint)
                                                                    (Ssequence
                                                                    (Sset _t'229
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'183
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'229 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'183
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'183 tint)
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
                                                                    (Sset _t'226
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _i_am_the_initiator
                                                                    tbool))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'226 tbool)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'227
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _remote_index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'228
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sset _t'184
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'227 tuint)
                                                                    (Etempvar _t'228 tuint)
                                                                    tint)
                                                                    tbool))))
                                                                    (Sset _t'184
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'184 tint)
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
                                                                    (Scall (Some _t'185)
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
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _first (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'185 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'187)
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
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Evar _second (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'186
                                                                    (Ecast
                                                                    (Etempvar _t'187 tint)
                                                                    tbool)))
                                                                    (Sset _t'186
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'186 tint)
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
                                                                    (Sset _t'224
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _is_valid
                                                                    tbool))
                                                                    (Sifthenelse (Etempvar _t'224 tbool)
                                                                    (Ssequence
                                                                    (Sset _t'225
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _is_valid
                                                                    tbool))
                                                                    (Sset _t'188
                                                                    (Ecast
                                                                    (Etempvar _t'225 tbool)
                                                                    tbool)))
                                                                    (Sset _t'188
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'188 tint)
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
                                                                    (Sset _t'222
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _birthdate
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'222 tulong)
                                                                    (Etempvar _now_a tulong)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'223
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _birthdate
                                                                    tulong))
                                                                    (Sset _t'189
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'223 tulong)
                                                                    (Etempvar _now_a tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'189
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'189 tint)
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
                                                                    (Ssequence
                                                                    (Sset _t'220
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'220 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'221
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _type
                                                                    tint))
                                                                    (Sset _t'190
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'221 tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'190
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'190 tint)
                                                                    (Ssequence
                                                                    (Sset _t'219
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _peer
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                    (Sset _t'191
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'219 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Eaddrof
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr)))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'191
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'191 tint)
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
                                                                    (Ssequence
                                                                    (Sset _t'217
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _index
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'218
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr)))
                                                                    (Tstruct _message_handshake_response noattr))
                                                                    _sender_index
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'217 tuint)
                                                                    (Etempvar _t'218 tuint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'193)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil))
                                                                    (Sset _t'192
                                                                    (Ecast
                                                                    (Etempvar _t'193 tint)
                                                                    tbool)))
                                                                    (Sset _t'192
                                                                    (Econst_int (Int.repr 0) tint)))))
                                                                    (Sifthenelse (Etempvar _t'192 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'195)
                                                                    (Evar _table_len 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    nil))
                                                                    (Sset _t'194
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'195 tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'194
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'194 tint)
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
                                                                    (Sset _t'216
                                                                    (Efield
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    _hashed
                                                                    tbool))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'216 tbool)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'197)
                                                                    (Evar _hs_zeroed_from 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _snap (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sset _t'196
                                                                    (Ecast
                                                                    (Etempvar _t'197 tint)
                                                                    tbool)))
                                                                    (Sset _t'196
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'196 tint)
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
                                                                    (Sset _t'215
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _internal_id
                                                                    tulong))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'215 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _id_a tulong)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tulong)
                                                                    tint)
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
                                                                    (Scall (Some _t'198)
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
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sifthenelse (Etempvar _t'198 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'200)
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
                                                                    (Etempvar _ka (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _receiving
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _kb (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Tstruct _noise_keypair noattr))
                                                                    _sending
                                                                    (Tstruct _noise_symmetric_key noattr))
                                                                    _key
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'199
                                                                    (Ecast
                                                                    (Etempvar _t'200 tint)
                                                                    tbool)))
                                                                    (Sset _t'199
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'199 tint)
                                                                    tint)
                                                                    (Scall None
                                                                    (Evar _check_failed 
                                                                    (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                                    nil)
                                                                    Sskip))
                                                                    Sbreak)))))))))))))))))))))))))))))))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _wg_noise_keypairs_clear 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_keypairs noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    (tptr (Tstruct _noise_keypairs noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _wg_noise_keypairs_clear 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _noise_keypairs noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    (tptr (Tstruct _noise_keypairs noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'213
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _current_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'213 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'214
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _keypairs
                                                                    (Tstruct _noise_keypairs noattr))
                                                                    _next_keypair
                                                                    (tptr (Tstruct _noise_keypair noattr))))
                                                                    (Sset _t'201
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'214 (tptr (Tstruct _noise_keypair noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'201
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'201 tint)
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
                                                                    (Sset _t'211
                                                                    (Efield
                                                                    (Evar _ita (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'211 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'212
                                                                    (Efield
                                                                    (Evar _itb (Tstruct _index_hashtable noattr))
                                                                    _head
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                                    (Sset _t'202
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'212 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                    (Ecast
                                                                    (Econst_int (Int.repr 0) tint)
                                                                    (tptr tvoid))
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'202
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'202 tint)
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
                                                                    (Ssequence
                                                                    (Sset _t'209
                                                                    (Evar _wg_shim_allocs tulong))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'209 tulong)
                                                                    (Etempvar _allocs0 tulong)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'210
                                                                    (Evar _wg_shim_frees tulong))
                                                                    (Sset _t'203
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Ebinop Osub
                                                                    (Etempvar _t'210 tulong)
                                                                    (Etempvar _frees0 tulong)
                                                                    tulong)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'203
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'203 tint)
                                                                    (Ssequence
                                                                    (Sset _t'208
                                                                    (Evar _wg_shim_alloc_failures tulong))
                                                                    (Sset _t'204
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'208 tulong)
                                                                    (Etempvar _fails0 tulong)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'204
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'204 tint)
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
                                                                    (Sset _t'206
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'206 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Sset _t'207
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'205
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'207 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'205
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'205 tint)
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
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m1 (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _quickproof_free 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Etempvar _m2 (tptr (Tstruct _message_handshake_response noattr))) ::
                                                                    nil))
                                                                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
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
 Composite _net_device Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _message_header Struct (Member_plain _type tuint :: nil) noattr ::
 Composite _message_macs Struct
   (Member_plain _mac1 (tarray tuchar 16) ::
    Member_plain _mac2 (tarray tuchar 16) :: nil)
   noattr ::
 Composite _message_handshake_initiation Struct
   (Member_plain _header (Tstruct _message_header noattr) ::
    Member_plain _sender_index tuint ::
    Member_plain _unencrypted_ephemeral (tarray tuchar 32) ::
    Member_plain _encrypted_static (tarray tuchar 48) ::
    Member_plain _encrypted_timestamp (tarray tuchar 28) ::
    Member_plain _macs (Tstruct _message_macs noattr) :: nil)
   noattr ::
 Composite _message_handshake_response Struct
   (Member_plain _header (Tstruct _message_header noattr) ::
    Member_plain _sender_index tuint :: Member_plain _receiver_index tuint ::
    Member_plain _unencrypted_ephemeral (tarray tuchar 32) ::
    Member_plain _encrypted_nothing (tarray tuchar 16) ::
    Member_plain _macs (Tstruct _message_macs noattr) :: nil)
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
 Composite _m_state Struct
   (Member_plain _ck (tarray tuchar 32) ::
    Member_plain _h (tarray tuchar 32) :: nil)
   noattr ::
 Composite _m_initiation Struct
   (Member_plain _ephemeral (tarray tuchar 32) ::
    Member_plain _enc_static (tarray tuchar 48) ::
    Member_plain _enc_timestamp (tarray tuchar 28) ::
    Member_plain _eph_priv (tarray tuchar 32) ::
    Member_plain _st (Tstruct _m_state noattr) :: nil)
   noattr ::
 Composite _m_consumed_initiation Struct
   (Member_plain _st (Tstruct _m_state noattr) ::
    Member_plain _key (tarray tuchar 32) ::
    Member_plain _spub (tarray tuchar 32) ::
    Member_plain _ts (tarray tuchar 12) :: nil)
   noattr ::
 Composite _m_response Struct
   (Member_plain _ephemeral (tarray tuchar 32) ::
    Member_plain _enc_nothing (tarray tuchar 16) ::
    Member_plain _eph_priv (tarray tuchar 32) ::
    Member_plain _st (Tstruct _m_state noattr) :: nil)
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
 (_curve25519_generic,
   Gfun(External (EF_external "curve25519_generic"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tvoid
     cc_default)) ::
 (_chacha20poly1305_encrypt,
   Gfun(External (EF_external "chacha20poly1305_encrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      tulong :: (tptr tuchar) :: nil) tvoid cc_default)) ::
 (_chacha20poly1305_decrypt,
   Gfun(External (EF_external "chacha20poly1305_decrypt"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xlong :: AST.Xptr ::
                      AST.Xlong :: AST.Xlong :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
      tulong :: (tptr tuchar) :: nil) tbool cc_default)) ::
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
 (_wg_noise_keypairs_clear,
   Gfun(External (EF_external "wg_noise_keypairs_clear"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _noise_keypairs noattr)) :: nil) tvoid cc_default)) ::
 (_wg_noise_set_static_identity_private_key,
   Gfun(External (EF_external "wg_noise_set_static_identity_private_key"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _noise_static_identity noattr)) :: (tptr tuchar) :: nil)
     tvoid cc_default)) ::
 (_wg_noise_handshake_create_initiation,
   Gfun(External (EF_external "wg_noise_handshake_create_initiation"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _message_handshake_initiation noattr)) ::
      (tptr (Tstruct _noise_handshake noattr)) :: nil) tbool cc_default)) ::
 (_wg_noise_handshake_consume_initiation,
   Gfun(External (EF_external "wg_noise_handshake_consume_initiation"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr
                     cc_default))
     ((tptr (Tstruct _message_handshake_initiation noattr)) ::
      (tptr (Tstruct _wg_device noattr)) :: nil)
     (tptr (Tstruct _wg_peer noattr)) cc_default)) ::
 (_wg_noise_handshake_create_response,
   Gfun(External (EF_external "wg_noise_handshake_create_response"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _message_handshake_response noattr)) ::
      (tptr (Tstruct _noise_handshake noattr)) :: nil) tbool cc_default)) ::
 (_wg_noise_handshake_consume_response,
   Gfun(External (EF_external "wg_noise_handshake_consume_response"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr
                     cc_default))
     ((tptr (Tstruct _message_handshake_response noattr)) ::
      (tptr (Tstruct _wg_device noattr)) :: nil)
     (tptr (Tstruct _wg_peer noattr)) cc_default)) ::
 (_wg_noise_handshake_begin_session,
   Gfun(External (EF_external "wg_noise_handshake_begin_session"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _noise_handshake noattr)) ::
      (tptr (Tstruct _noise_keypairs noattr)) :: nil) tbool cc_default)) ::
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
 (_wg_cookie_add_mac_to_packet,
   Gfun(External (EF_external "wg_cookie_add_mac_to_packet"
                   (mksignature (AST.Xptr :: AST.Xlong :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr tvoid) :: tulong :: (tptr (Tstruct _wg_peer noattr)) :: nil)
     tvoid cc_default)) ::
 (_wg_peer_put,
   Gfun(External (EF_external "wg_peer_put"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _wg_peer noattr)) :: nil) tvoid cc_default)) ::
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_bytes_set, Gfun(Internal f_bytes_set)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_draw_boottime, Gfun(Internal f_draw_boottime)) ::
 (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_real_sec, Gvar v_wg_shim_real_sec) ::
 (_wg_shim_real_nsec, Gvar v_wg_shim_real_nsec) ::
 (_wg_shim_random_log, Gvar v_wg_shim_random_log) ::
 (_wg_shim_random_u32, Gvar v_wg_shim_random_u32) ::
 (_wg_shim_allocs, Gvar v_wg_shim_allocs) ::
 (_wg_shim_alloc_failures, Gvar v_wg_shim_alloc_failures) ::
 (_wg_shim_frees, Gvar v_wg_shim_frees) ::
 (_wg_shim_ratelimit_allow, Gvar v_wg_shim_ratelimit_allow) ::
 (_le32_store, Gfun(Internal f_le32_store)) ::
 (_m_hash2, Gfun(Internal f_m_hash2)) ::
 (_m_hmac, Gfun(Internal f_m_hmac)) :: (_m_kdf, Gfun(Internal f_m_kdf)) ::
 (_m_dh, Gfun(Internal f_m_dh)) :: (_x_handshake__M_BASEPOINT, Gvar v_x_handshake__M_BASEPOINT) ::
 (_m_clamp, Gfun(Internal f_m_clamp)) ::
 (_m_identity_of, Gfun(Internal f_m_identity_of)) ::
 (_x_handshake__M_CONSTRUCTION, Gvar v_x_handshake__M_CONSTRUCTION) ::
 (_x_handshake__M_IDENTIFIER, Gvar v_x_handshake__M_IDENTIFIER) ::
 (_m_start, Gfun(Internal f_m_start)) ::
 (_m_mix_hash, Gfun(Internal f_m_mix_hash)) ::
 (_m_mix_ck, Gfun(Internal f_m_mix_ck)) ::
 (_m_mix_key, Gfun(Internal f_m_mix_key)) ::
 (_m_mix_psk, Gfun(Internal f_m_mix_psk)) ::
 (_m_encrypt_and_hash, Gfun(Internal f_m_encrypt_and_hash)) ::
 (_m_decrypt_and_hash, Gfun(Internal f_m_decrypt_and_hash)) ::
 (_m_tai64n, Gfun(Internal f_m_tai64n)) ::
 (_m_create_initiation, Gfun(Internal f_m_create_initiation)) ::
 (_m_consume_initiation_1, Gfun(Internal f_m_consume_initiation_1)) ::
 (_m_consume_initiation_2, Gfun(Internal f_m_consume_initiation_2)) ::
 (_m_create_response, Gfun(Internal f_m_create_response)) ::
 (_m_consume_response, Gfun(Internal f_m_consume_response)) ::
 (_m_transport, Gfun(Internal f_m_transport)) ::
 (_x_handshake__M_LABEL_MAC1, Gvar v_x_handshake__M_LABEL_MAC1) ::
 (_x_handshake__M_LABEL_COOKIE, Gvar v_x_handshake__M_LABEL_COOKIE) ::
 (_m_label_key, Gfun(Internal f_m_label_key)) ::
 (_m_mac, Gfun(Internal f_m_mac)) ::
 (_setup_device, Gfun(Internal f_setup_device)) ::
 (_setup_peer, Gfun(Internal f_setup_peer)) ::
 (_m_precomputed, Gfun(Internal f_m_precomputed)) ::
 (_table_has, Gfun(Internal f_table_has)) ::
 (_table_index_unique, Gfun(Internal f_table_index_unique)) ::
 (_table_len, Gfun(Internal f_table_len)) ::
 (_hs_take, Gfun(Internal f_hs_take)) ::
 (_hs_same, Gfun(Internal f_hs_same)) ::
 (_hs_zeroed_from, Gfun(Internal f_hs_zeroed_from)) ::
 (_m_static_public_field, Gfun(Internal f_m_static_public_field)) ::
 (_init_img, Gfun(Internal f_init_img)) ::
 (_resp_img, Gfun(Internal f_resp_img)) ::
 (_fill_init, Gfun(Internal f_fill_init)) ::
 (_fill_resp, Gfun(Internal f_fill_resp)) ::
 (_draw_real_clock, Gfun(Internal f_draw_real_clock)) ::
 (_m_ts_newer, Gfun(Internal f_m_ts_newer)) ::
 (_m_not_flood, Gfun(Internal f_m_not_flood)) ::
 (_m_last_consumption, Gfun(Internal f_m_last_consumption)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_shim_ratelimit_allow :: _wg_shim_frees ::
 _wg_shim_alloc_failures :: _wg_shim_allocs :: _wg_shim_random_u32 ::
 _wg_shim_random_log :: _wg_shim_real_nsec :: _wg_shim_real_sec ::
 _wg_shim_boottime_ns :: _wg_peer_put :: _wg_cookie_add_mac_to_packet ::
 _wg_cookie_init :: _wg_cookie_checker_precompute_peer_keys ::
 _wg_cookie_checker_precompute_device_keys :: _wg_cookie_checker_init ::
 _wg_noise_handshake_begin_session :: _wg_noise_handshake_consume_response ::
 _wg_noise_handshake_create_response ::
 _wg_noise_handshake_consume_initiation ::
 _wg_noise_handshake_create_initiation ::
 _wg_noise_set_static_identity_private_key :: _wg_noise_keypairs_clear ::
 _wg_noise_handshake_init :: _wg_noise_init :: _blake2s_final ::
 _blake2s_update :: _chacha20poly1305_decrypt :: _chacha20poly1305_encrypt ::
 _curve25519_generic :: _quickproof_free :: _quickproof_malloc :: _memset ::
 _memcpy :: _nondet_bytes :: _nondet_u32 :: _nondet_u8 :: ___builtin_debug ::
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


