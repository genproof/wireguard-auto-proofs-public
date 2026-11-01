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
  Definition source_file := "harness/x_replay.c".
  Definition normalized := true.
End Info.

Definition _x_replay__M_BASEPOINT : ident := $"x_replay__M_BASEPOINT".
Definition _x_replay__M_CONSTRUCTION : ident := $"x_replay__M_CONSTRUCTION".
Definition _x_replay__M_IDENTIFIER : ident := $"x_replay__M_IDENTIFIER".
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
Definition _acc : ident := $"acc".
Definition _accepted : ident := $"accepted".
Definition _alen : ident := $"alen".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
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
Definition _chaining_key : ident := $"chaining_key".
Definition _check_failed : ident := $"check_failed".
Definition _ci : ident := $"ci".
Definition _ck : ident := $"ck".
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _copy_init : ident := $"copy_init".
Definition _counter : ident := $"counter".
Definition _ctx : ident := $"ctx".
Definition _current_keypair : ident := $"current_keypair".
Definition _curve25519_generic : ident := $"curve25519_generic".
Definition _d : ident := $"d".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _dh : ident := $"dh".
Definition _draw_boottime : ident := $"draw_boottime".
Definition _draw_real_clock : ident := $"draw_real_clock".
Definition _draw_steps : ident := $"draw_steps".
Definition _draw_u64 : ident := $"draw_u64".
Definition _enc_static : ident := $"enc_static".
Definition _enc_timestamp : ident := $"enc_timestamp".
Definition _encrypted_static : ident := $"encrypted_static".
Definition _encrypted_timestamp : ident := $"encrypted_timestamp".
Definition _entry : ident := $"entry".
Definition _ephemeral : ident := $"ephemeral".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _f : ident := $"f".
Definition _fill_init : ident := $"fill_init".
Definition _h : ident := $"h".
Definition _h0 : ident := $"h0".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_accepted : ident := $"have_accepted".
Definition _have_sent : ident := $"have_sent".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _header : ident := $"header".
Definition _hi : ident := $"hi".
Definition _hs_same : ident := $"hs_same".
Definition _hs_snap : ident := $"hs_snap".
Definition _hs_take : ident := $"hs_take".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _ia : ident := $"ia".
Definition _ib : ident := $"ib".
Definition _id : ident := $"id".
Definition _in : ident := $"in".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _inlen : ident := $"inlen".
Definition _inner : ident := $"inner".
Definition _internal_id : ident := $"internal_id".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _ita : ident := $"ita".
Definition _itab : ident := $"itab".
Definition _itb : ident := $"itb".
Definition _k : ident := $"k".
Definition _key : ident := $"key".
Definition _keylen : ident := $"keylen".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kind : ident := $"kind".
Definition _kref : ident := $"kref".
Definition _last : ident := $"last".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest : ident := $"latest".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _lock : ident := $"lock".
Definition _m : ident := $"m".
Definition _m_clamp : ident := $"m_clamp".
Definition _m_consume_initiation_1 : ident := $"m_consume_initiation_1".
Definition _m_consume_initiation_2 : ident := $"m_consume_initiation_2".
Definition _m_consumed_initiation : ident := $"m_consumed_initiation".
Definition _m_decrypt_and_hash : ident := $"m_decrypt_and_hash".
Definition _m_dh : ident := $"m_dh".
Definition _m_hash2 : ident := $"m_hash2".
Definition _m_hmac : ident := $"m_hmac".
Definition _m_identity : ident := $"m_identity".
Definition _m_identity_of : ident := $"m_identity_of".
Definition _m_kdf : ident := $"m_kdf".
Definition _m_last_consumption : ident := $"m_last_consumption".
Definition _m_mix_ck : ident := $"m_mix_ck".
Definition _m_mix_hash : ident := $"m_mix_hash".
Definition _m_mix_key : ident := $"m_mix_key".
Definition _m_not_flood : ident := $"m_not_flood".
Definition _m_precomputed : ident := $"m_precomputed".
Definition _m_start : ident := $"m_start".
Definition _m_state : ident := $"m_state".
Definition _m_ts_newer : ident := $"m_ts_newer".
Definition _mac1 : ident := $"mac1".
Definition _mac2 : ident := $"mac2".
Definition _macs : ident := $"macs".
Definition _main : ident := $"main".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _message_handshake_initiation : ident := $"message_handshake_initiation".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _message_macs : ident := $"message_macs".
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
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
Definition _now : ident := $"now".
Definition _o : ident := $"o".
Definition _ok : ident := $"ok".
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
Definition _raw : ident := $"raw".
Definition _raw_a : ident := $"raw_a".
Definition _raw_b : ident := $"raw_b".
Definition _raw_priv : ident := $"raw_priv".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
Definition _responder_pub : ident := $"responder_pub".
Definition _ret : ident := $"ret".
Definition _rid : ident := $"rid".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s : ident := $"s".
Definition _secret : ident := $"secret".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sender_index : ident := $"sender_index".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _sent : ident := $"sent".
Definition _setup_device : ident := $"setup_device".
Definition _setup_peer : ident := $"setup_peer".
Definition _snap : ident := $"snap".
Definition _spub : ident := $"spub".
Definition _ss : ident := $"ss".
Definition _ss_b : ident := $"ss_b".
Definition _st : ident := $"st".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _steps : ident := $"steps".
Definition _t : ident := $"t".
Definition _t1 : ident := $"t1".
Definition _t2 : ident := $"t2".
Definition _t3 : ident := $"t3".
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
Definition _wg_noise_handshake_consume_initiation : ident := $"wg_noise_handshake_consume_initiation".
Definition _wg_noise_handshake_create_initiation : ident := $"wg_noise_handshake_create_initiation".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_init : ident := $"wg_noise_init".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_peer_put : ident := $"wg_peer_put".
Definition _wg_shim_boottime_ns : ident := $"wg_shim_boottime_ns".
Definition _wg_shim_real_nsec : ident := $"wg_shim_real_nsec".
Definition _wg_shim_real_sec : ident := $"wg_shim_real_sec".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition v_x_replay__M_BASEPOINT := {|
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
           (Evar _x_replay__M_BASEPOINT (tarray tuchar 32)) :: nil))
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

Definition v_x_replay__M_CONSTRUCTION := {|
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

Definition v_x_replay__M_IDENTIFIER := {|
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
     (Evar _x_replay__M_CONSTRUCTION (tarray tuchar 37)) ::
     (Econst_int (Int.repr 37) tint) ::
     (Evar _x_replay__M_CONSTRUCTION (tarray tuchar 37)) ::
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
       (Evar _x_replay__M_IDENTIFIER (tarray tuchar 34)) ::
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

Definition f_copy_init := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_d, (tptr (Tstruct _message_handshake_initiation noattr))) ::
                (_s, (tptr (Tstruct _message_handshake_initiation noattr))) ::
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
            (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _header
          (Tstruct _message_header noattr)) _type tuint))
    (Sassign
      (Efield
        (Efield
          (Ederef
            (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _header
          (Tstruct _message_header noattr)) _type tuint)
      (Etempvar _t'2 tuint)))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Ederef
            (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _sender_index
          tuint))
      (Sassign
        (Efield
          (Ederef
            (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
            (Tstruct _message_handshake_initiation noattr)) _sender_index
          tuint) (Etempvar _t'1 tuint)))
    (Ssequence
      (Scall None
        (Evar _bytes_copy (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                            tvoid cc_default))
        ((Efield
           (Ederef
             (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
             (Tstruct _message_handshake_initiation noattr))
           _unencrypted_ephemeral (tarray tuchar 32)) ::
         (Efield
           (Ederef
             (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
             (Tstruct _message_handshake_initiation noattr))
           _unencrypted_ephemeral (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _bytes_copy (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                               nil) tvoid cc_default))
          ((Efield
             (Ederef
               (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
               (Tstruct _message_handshake_initiation noattr))
             _encrypted_static (tarray tuchar 48)) ::
           (Efield
             (Ederef
               (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
               (Tstruct _message_handshake_initiation noattr))
             _encrypted_static (tarray tuchar 48)) ::
           (Econst_int (Int.repr 48) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _bytes_copy (Tfunction
                                ((tptr tuchar) :: (tptr tuchar) :: tulong ::
                                 nil) tvoid cc_default))
            ((Efield
               (Ederef
                 (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
                 (Tstruct _message_handshake_initiation noattr))
               _encrypted_timestamp (tarray tuchar 28)) ::
             (Efield
               (Ederef
                 (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
                 (Tstruct _message_handshake_initiation noattr))
               _encrypted_timestamp (tarray tuchar 28)) ::
             (Econst_int (Int.repr 28) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _bytes_copy (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   tulong :: nil) tvoid cc_default))
              ((Efield
                 (Efield
                   (Ederef
                     (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr)) _macs
                   (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 16) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _bytes_copy (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     tulong :: nil) tvoid cc_default))
                ((Efield
                   (Efield
                     (Ederef
                       (Etempvar _d (tptr (Tstruct _message_handshake_initiation noattr)))
                       (Tstruct _message_handshake_initiation noattr)) _macs
                     (Tstruct _message_macs noattr)) _mac2
                   (tarray tuchar 16)) ::
                 (Efield
                   (Efield
                     (Ederef
                       (Etempvar _s (tptr (Tstruct _message_handshake_initiation noattr)))
                       (Tstruct _message_handshake_initiation noattr)) _macs
                     (Tstruct _message_macs noattr)) _mac2
                   (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) ::
                 nil))
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))
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
              (_pa, (Tstruct _wg_peer noattr)) ::
              (_pb, (Tstruct _wg_peer noattr)) ::
              (_ia, (Tstruct _m_identity noattr)) ::
              (_ib, (Tstruct _m_identity noattr)) ::
              (_raw_a, (tarray tuchar 32)) :: (_raw_b, (tarray tuchar 32)) ::
              (_psk, (tarray tuchar 32)) :: (_ss_b, (tarray tuchar 32)) ::
              (_latest, (tarray tuchar 12)) ::
              (_ci, (Tstruct _m_consumed_initiation noattr)) ::
              (_snap, (Tstruct _hs_snap noattr)) :: nil);
  fn_temps := ((_sent, (tptr (Tstruct _message_handshake_initiation noattr))) ::
               (_accepted,
                (tptr (Tstruct _message_handshake_initiation noattr))) ::
               (_m, (tptr (Tstruct _message_handshake_initiation noattr))) ::
               (_ret, (tptr (Tstruct _wg_peer noattr))) ::
               (_have_sent, tint) :: (_have_accepted, tint) ::
               (_use_psk, tint) :: (_kind, tint) :: (_acc, tint) ::
               (_steps, tulong) :: (_i, tulong) :: (_now, tulong) ::
               (_last, tulong) :: (_d, tulong) :: (_t'36, tulong) ::
               (_t'35, tint) :: (_t'34, tint) :: (_t'33, tint) ::
               (_t'32, tulong) :: (_t'31, tint) :: (_t'30, tint) ::
               (_t'29, tint) :: (_t'28, tint) :: (_t'27, tint) ::
               (_t'26, tint) :: (_t'25, tint) :: (_t'24, tint) ::
               (_t'23, tint) :: (_t'22, tint) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'15, tuchar) :: (_t'14, tulong) :: (_t'13, tbool) ::
               (_t'12, tuchar) :: (_t'11, tulong) :: (_t'10, tulong) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, (tptr tvoid)) ::
               (_t'6, (tptr tvoid)) :: (_t'5, (tptr tvoid)) ::
               (_t'4, (tptr tvoid)) :: (_t'3, (tptr tvoid)) ::
               (_t'2, tuchar) :: (_t'1, tulong) :: (_t'42, tint) ::
               (_t'41, tuint) :: (_t'40, tuint) :: (_t'39, tuint) ::
               (_t'38, tint) :: (_t'37, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _have_sent (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sset _have_accepted (Econst_int (Int.repr 0) tint))
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
                (Ssequence
                  (Scall (Some _t'2)
                    (Evar _nondet_u8 (Tfunction nil tuchar cc_default)) nil)
                  (Sset _use_psk
                    (Ebinop Oand (Etempvar _t'2 tuchar)
                      (Econst_int (Int.repr 1) tint) tint)))
                (Ssequence
                  (Scall None
                    (Evar _nondet_bytes (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                    ((Evar _psk (tarray tuchar 32)) ::
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
                                               (tptr tuchar) :: nil) tvoid
                                              cc_default))
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
                                                  (tptr tuchar) :: nil) tvoid
                                                 cc_default))
                          ((Eaddrof (Evar _ia (Tstruct _m_identity noattr))
                             (tptr (Tstruct _m_identity noattr))) ::
                           (Evar _raw_a (tarray tuchar 32)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _m_identity_of (Tfunction
                                                   ((tptr (Tstruct _m_identity noattr)) ::
                                                    (tptr tuchar) :: nil)
                                                   tvoid cc_default))
                            ((Eaddrof (Evar _ib (Tstruct _m_identity noattr))
                               (tptr (Tstruct _m_identity noattr))) ::
                             (Evar _raw_b (tarray tuchar 32)) :: nil))
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Etempvar _use_psk tint)
                                (Sset _t'3
                                  (Ecast (Evar _psk (tarray tuchar 32))
                                    (tptr tvoid)))
                                (Sset _t'3
                                  (Ecast
                                    (Ecast (Econst_int (Int.repr 0) tint)
                                      (tptr tvoid)) (tptr tvoid))))
                              (Scall None
                                (Evar _setup_peer (Tfunction
                                                    ((tptr (Tstruct _wg_peer noattr)) ::
                                                     (tptr (Tstruct _wg_device noattr)) ::
                                                     (tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tvoid
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
                                 (Etempvar _t'3 (tptr tvoid)) ::
                                 (Econst_int (Int.repr 1) tint) :: nil)))
                            (Ssequence
                              (Ssequence
                                (Sifthenelse (Etempvar _use_psk tint)
                                  (Sset _t'4
                                    (Ecast (Evar _psk (tarray tuchar 32))
                                      (tptr tvoid)))
                                  (Sset _t'4
                                    (Ecast
                                      (Ecast (Econst_int (Int.repr 0) tint)
                                        (tptr tvoid)) (tptr tvoid))))
                                (Scall None
                                  (Evar _setup_peer (Tfunction
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
                                     _pub (tarray tuchar 32)) ::
                                   (Etempvar _t'4 (tptr tvoid)) ::
                                   (Econst_int (Int.repr 2) tint) :: nil)))
                              (Ssequence
                                (Scall None
                                  (Evar _m_precomputed (Tfunction
                                                         ((tptr tuchar) ::
                                                          (tptr (Tstruct _m_identity noattr)) ::
                                                          (tptr tuchar) ::
                                                          nil) tvoid
                                                         cc_default))
                                  ((Evar _ss_b (tarray tuchar 32)) ::
                                   (Eaddrof
                                     (Evar _ib (Tstruct _m_identity noattr))
                                     (tptr (Tstruct _m_identity noattr))) ::
                                   (Efield
                                     (Evar _ia (Tstruct _m_identity noattr))
                                     _pub (tarray tuchar 32)) :: nil))
                                (Ssequence
                                  (Ssequence
                                    (Scall (Some _t'5)
                                      (Evar _quickproof_malloc (Tfunction
                                                                 (tulong ::
                                                                  nil)
                                                                 (tptr tvoid)
                                                                 cc_default))
                                      ((Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                       nil))
                                    (Sset _sent (Etempvar _t'5 (tptr tvoid))))
                                  (Ssequence
                                    (Ssequence
                                      (Scall (Some _t'6)
                                        (Evar _quickproof_malloc (Tfunction
                                                                   (tulong ::
                                                                    nil)
                                                                   (tptr tvoid)
                                                                   cc_default))
                                        ((Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                         nil))
                                      (Sset _accepted
                                        (Etempvar _t'6 (tptr tvoid))))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'7)
                                          (Evar _quickproof_malloc (Tfunction
                                                                    (tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                          ((Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                           nil))
                                        (Sset _m
                                          (Etempvar _t'7 (tptr tvoid))))
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Sifthenelse (Ebinop Oeq
                                                           (Etempvar _sent (tptr (Tstruct _message_handshake_initiation noattr)))
                                                           (Ecast
                                                             (Econst_int (Int.repr 0) tint)
                                                             (tptr tvoid))
                                                           tint)
                                              (Sset _t'8
                                                (Econst_int (Int.repr 1) tint))
                                              (Sset _t'8
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _accepted (tptr (Tstruct _message_handshake_initiation noattr)))
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
                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
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
                                                ((Etempvar _sent (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                 nil))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _quickproof_free 
                                                  (Tfunction
                                                    ((tptr tvoid) :: nil)
                                                    tvoid cc_default))
                                                  ((Etempvar _accepted (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _quickproof_free 
                                                    (Tfunction
                                                      ((tptr tvoid) :: nil)
                                                      tvoid cc_default))
                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                     nil))
                                                  (Sreturn (Some (Econst_int (Int.repr 0) tint))))))
                                            Sskip))
                                        (Ssequence
                                          (Scall None
                                            (Evar _bytes_set (Tfunction
                                                               ((tptr tuchar) ::
                                                                tuchar ::
                                                                tulong ::
                                                                nil) tvoid
                                                               cc_default))
                                            ((Evar _latest (tarray tuchar 12)) ::
                                             (Econst_int (Int.repr 0) tint) ::
                                             (Econst_int (Int.repr 12) tint) ::
                                             nil))
                                          (Ssequence
                                            (Sset _last
                                              (Ecast
                                                (Econst_int (Int.repr 0) tint)
                                                tulong))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'10)
                                                  (Evar _draw_boottime 
                                                  (Tfunction nil tulong
                                                    cc_default)) nil)
                                                (Sset _now
                                                  (Etempvar _t'10 tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Scall (Some _t'11)
                                                    (Evar _draw_steps 
                                                    (Tfunction nil tulong
                                                      cc_default)) nil)
                                                  (Sset _steps
                                                    (Etempvar _t'11 tulong)))
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
                                                            (Etempvar _steps tulong)
                                                            tint)
                                                          Sskip
                                                          Sbreak)
                                                        (Ssequence
                                                          (Ssequence
                                                            (Scall (Some _t'12)
                                                              (Evar _nondet_u8 
                                                              (Tfunction nil
                                                                tuchar
                                                                cc_default))
                                                              nil)
                                                            (Sset _kind
                                                              (Ebinop Omod
                                                                (Etempvar _t'12 tuchar)
                                                                (Econst_int (Int.repr 3) tint)
                                                                tint)))
                                                          (Ssequence
                                                            (Sifthenelse 
                                                              (Ebinop Oeq
                                                                (Etempvar _kind tint)
                                                                (Econst_int (Int.repr 0) tint)
                                                                tint)
                                                              (Ssequence
                                                                (Scall None
                                                                  (Evar _fill_init 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                  ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
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
                                                                    (Scall (Some _t'13)
                                                                    (Evar _wg_noise_handshake_create_initiation 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tbool
                                                                    cc_default))
                                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                    nil))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'13 tbool)
                                                                    tint)
                                                                    Scontinue
                                                                    Sskip))
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
                                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Esizeof (Tstruct _message_handshake_initiation noattr) tulong) ::
                                                                    (Eaddrof
                                                                    (Evar _pb (Tstruct _wg_peer noattr))
                                                                    (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _copy_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _sent (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Sset _have_sent
                                                                    (Econst_int (Int.repr 1) tint)))))))
                                                              (Sifthenelse 
                                                                (Ebinop Oeq
                                                                  (Etempvar _kind tint)
                                                                  (Econst_int (Int.repr 1) tint)
                                                                  tint)
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _have_sent tint)
                                                                    tint)
                                                                    Scontinue
                                                                    Sskip)
                                                                  (Scall None
                                                                    (Evar _copy_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Etempvar _sent (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil)))
                                                                (Ssequence
                                                                  (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _have_accepted tint)
                                                                    tint)
                                                                    Scontinue
                                                                    Sskip)
                                                                  (Scall None
                                                                    (Evar _copy_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Etempvar _accepted (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil)))))
                                                            (Ssequence
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Ssequence
                                                                    (Scall (Some _t'14)
                                                                    (Evar _draw_u64 
                                                                    (Tfunction
                                                                    nil
                                                                    tulong
                                                                    cc_default))
                                                                    nil)
                                                                    (Scall (Some _t'15)
                                                                    (Evar _nondet_u8 
                                                                    (Tfunction
                                                                    nil
                                                                    tuchar
                                                                    cc_default))
                                                                    nil))
                                                                  (Sset _d
                                                                    (Ebinop Oshr
                                                                    (Etempvar _t'14 tulong)
                                                                    (Ebinop Omod
                                                                    (Etempvar _t'15 tuchar)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    tulong)))
                                                                (Sifthenelse 
                                                                  (Ebinop Olt
                                                                    (Etempvar _d tulong)
                                                                    (Ebinop Osub
                                                                    (Ebinop Oshl
                                                                    (Econst_long (Int64.repr 1) tulong)
                                                                    (Econst_int (Int.repr 62) tint)
                                                                    tulong)
                                                                    (Etempvar _now tulong)
                                                                    tulong)
                                                                    tint)
                                                                  (Sset _now
                                                                    (Ebinop Oadd
                                                                    (Etempvar _now tulong)
                                                                    (Etempvar _d tulong)
                                                                    tulong))
                                                                  Sskip))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Evar _wg_shim_boottime_ns tulong)
                                                                  (Etempvar _now tulong))
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
                                                                    (Scall (Some _t'16)
                                                                    (Evar _wg_noise_handshake_consume_initiation 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _wg_device noattr)) ::
                                                                    nil)
                                                                    (tptr (Tstruct _wg_peer noattr))
                                                                    cc_default))
                                                                    ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Eaddrof
                                                                    (Evar _wb (Tstruct _wg_device noattr))
                                                                    (tptr (Tstruct _wg_device noattr))) ::
                                                                    nil))
                                                                    (Sset _ret
                                                                    (Etempvar _t'16 (tptr (Tstruct _wg_peer noattr)))))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _t'42
                                                                    (Efield
                                                                    (Evar _ib (Tstruct _m_identity noattr))
                                                                    _ok tint))
                                                                    (Sifthenelse (Etempvar _t'42 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'18)
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
                                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _unencrypted_ephemeral
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_static
                                                                    (tarray tuchar 48)) ::
                                                                    nil))
                                                                    (Sset _t'17
                                                                    (Ecast
                                                                    (Etempvar _t'18 tint)
                                                                    tbool)))
                                                                    (Sset _t'17
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'17 tint)
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
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _spub
                                                                    (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Evar _ia (Tstruct _m_identity noattr))
                                                                    _pub
                                                                    (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Sset _t'19
                                                                    (Ecast
                                                                    (Etempvar _t'20 tint)
                                                                    tbool)))
                                                                    (Sset _t'19
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'19 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'22)
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
                                                                    (Evar _ss_b (tarray tuchar 32)) ::
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr)))
                                                                    (Tstruct _message_handshake_initiation noattr))
                                                                    _encrypted_timestamp
                                                                    (tarray tuchar 28)) ::
                                                                    nil))
                                                                    (Sset _t'21
                                                                    (Ecast
                                                                    (Etempvar _t'22 tint)
                                                                    tbool)))
                                                                    (Sset _t'21
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'21 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'24)
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
                                                                    (Evar _latest (tarray tuchar 12)) ::
                                                                    nil))
                                                                    (Sset _t'23
                                                                    (Ecast
                                                                    (Etempvar _t'24 tint)
                                                                    tbool)))
                                                                    (Sset _t'23
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse (Etempvar _t'23 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'26)
                                                                    (Evar _m_not_flood 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _last tulong) ::
                                                                    (Etempvar _now tulong) ::
                                                                    nil))
                                                                    (Sset _t'25
                                                                    (Ecast
                                                                    (Etempvar _t'26 tint)
                                                                    tbool)))
                                                                    (Sset _t'25
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sset _acc
                                                                    (Etempvar _t'25 tint)))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Oeq
                                                                    (Etempvar _kind tint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    (Sloop
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc tint)
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
                                                                    Sskip)
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _acc tint)
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
                                                                    (Scall (Some _t'28)
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
                                                                    (Sset _t'27
                                                                    (Ecast
                                                                    (Etempvar _t'28 tint)
                                                                    tbool)))
                                                                    (Sset _t'27
                                                                    (Econst_int (Int.repr 0) tint)))
                                                                    (Sifthenelse (Etempvar _t'27 tint)
                                                                    (Ssequence
                                                                    (Sset _t'41
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'29
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'41 tuint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'29
                                                                    (Econst_int (Int.repr 0) tint))))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'29 tint)
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
                                                                    (Sset _t'40
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sset _t'30
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'40 tuint)
                                                                    (Econst_int (Int.repr 2) tint)
                                                                    tint)
                                                                    tbool)))
                                                                    (Sset _t'30
                                                                    (Econst_int (Int.repr 0) tint)))
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
                                                                    (Sset _t'39
                                                                    (Efield
                                                                    (Efield
                                                                    (Evar _pa (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'39 tuint)
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
                                                                    (Sset _t'38
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
                                                                    (Etempvar _t'38 tint)
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
                                                                    (Scall (Some _t'31)
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
                                                                    (Sifthenelse 
                                                                    (Eunop Onotbool
                                                                    (Etempvar _t'31 tint)
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
                                                                    (Scall (Some _t'32)
                                                                    (Evar _m_last_consumption 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _last tulong) ::
                                                                    (Etempvar _now tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Sset _t'37
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
                                                                    (Etempvar _t'37 tulong)
                                                                    (Etempvar _t'32 tulong)
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
                                                                    (Scall (Some _t'33)
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
                                                                    (Sifthenelse (Etempvar _t'33 tint)
                                                                    (Ssequence
                                                                    (Scall (Some _t'35)
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
                                                                    (Sset _t'34
                                                                    (Ecast
                                                                    (Etempvar _t'35 tint)
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
                                                                    (Scall None
                                                                    (Evar _bytes_copy 
                                                                    (Tfunction
                                                                    ((tptr tuchar) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _latest (tarray tuchar 12)) ::
                                                                    (Efield
                                                                    (Evar _ci (Tstruct _m_consumed_initiation noattr))
                                                                    _ts
                                                                    (tarray tuchar 12)) ::
                                                                    (Econst_int (Int.repr 12) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Scall (Some _t'36)
                                                                    (Evar _m_last_consumption 
                                                                    (Tfunction
                                                                    (tulong ::
                                                                    tulong ::
                                                                    nil)
                                                                    tulong
                                                                    cc_default))
                                                                    ((Etempvar _last tulong) ::
                                                                    (Etempvar _now tulong) ::
                                                                    nil))
                                                                    (Sset _last
                                                                    (Etempvar _t'36 tulong)))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _copy_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    (tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Etempvar _accepted (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    (Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                                    nil))
                                                                    (Sset _have_accepted
                                                                    (Econst_int (Int.repr 1) tint))))))))))))))))))))))
                                                      (Sset _i
                                                        (Ebinop Oadd
                                                          (Etempvar _i tulong)
                                                          (Econst_int (Int.repr 1) tint)
                                                          tulong))))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _quickproof_free 
                                                      (Tfunction
                                                        ((tptr tvoid) :: nil)
                                                        tvoid cc_default))
                                                      ((Etempvar _sent (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Scall None
                                                        (Evar _quickproof_free 
                                                        (Tfunction
                                                          ((tptr tvoid) ::
                                                           nil) tvoid
                                                          cc_default))
                                                        ((Etempvar _accepted (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                         nil))
                                                      (Ssequence
                                                        (Scall None
                                                          (Evar _quickproof_free 
                                                          (Tfunction
                                                            ((tptr tvoid) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Etempvar _m (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                                           nil))
                                                        (Sreturn (Some (Econst_int (Int.repr 0) tint))))))))))))))))))))))))))))))
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
 Composite _m_consumed_initiation Struct
   (Member_plain _st (Tstruct _m_state noattr) ::
    Member_plain _key (tarray tuchar 32) ::
    Member_plain _spub (tarray tuchar 32) ::
    Member_plain _ts (tarray tuchar 12) :: nil)
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
 (_curve25519_generic,
   Gfun(External (EF_external "curve25519_generic"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xvoid cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tvoid
     cc_default)) ::
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
     cc_default)) ::
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
 (_draw_steps, Gfun(Internal f_draw_steps)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_draw_boottime, Gfun(Internal f_draw_boottime)) ::
 (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_real_sec, Gvar v_wg_shim_real_sec) ::
 (_wg_shim_real_nsec, Gvar v_wg_shim_real_nsec) ::
 (_m_hash2, Gfun(Internal f_m_hash2)) ::
 (_m_hmac, Gfun(Internal f_m_hmac)) :: (_m_kdf, Gfun(Internal f_m_kdf)) ::
 (_m_dh, Gfun(Internal f_m_dh)) :: (_x_replay__M_BASEPOINT, Gvar v_x_replay__M_BASEPOINT) ::
 (_m_clamp, Gfun(Internal f_m_clamp)) ::
 (_m_identity_of, Gfun(Internal f_m_identity_of)) ::
 (_x_replay__M_CONSTRUCTION, Gvar v_x_replay__M_CONSTRUCTION) ::
 (_x_replay__M_IDENTIFIER, Gvar v_x_replay__M_IDENTIFIER) ::
 (_m_start, Gfun(Internal f_m_start)) ::
 (_m_mix_hash, Gfun(Internal f_m_mix_hash)) ::
 (_m_mix_ck, Gfun(Internal f_m_mix_ck)) ::
 (_m_mix_key, Gfun(Internal f_m_mix_key)) ::
 (_m_decrypt_and_hash, Gfun(Internal f_m_decrypt_and_hash)) ::
 (_m_consume_initiation_1, Gfun(Internal f_m_consume_initiation_1)) ::
 (_m_consume_initiation_2, Gfun(Internal f_m_consume_initiation_2)) ::
 (_setup_device, Gfun(Internal f_setup_device)) ::
 (_setup_peer, Gfun(Internal f_setup_peer)) ::
 (_m_precomputed, Gfun(Internal f_m_precomputed)) ::
 (_hs_take, Gfun(Internal f_hs_take)) ::
 (_hs_same, Gfun(Internal f_hs_same)) ::
 (_fill_init, Gfun(Internal f_fill_init)) ::
 (_draw_real_clock, Gfun(Internal f_draw_real_clock)) ::
 (_m_ts_newer, Gfun(Internal f_m_ts_newer)) ::
 (_m_not_flood, Gfun(Internal f_m_not_flood)) ::
 (_m_last_consumption, Gfun(Internal f_m_last_consumption)) ::
 (_copy_init, Gfun(Internal f_copy_init)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_shim_real_nsec :: _wg_shim_real_sec :: _wg_shim_boottime_ns ::
 _wg_peer_put :: _wg_cookie_add_mac_to_packet :: _wg_cookie_init ::
 _wg_cookie_checker_precompute_peer_keys ::
 _wg_cookie_checker_precompute_device_keys :: _wg_cookie_checker_init ::
 _wg_noise_handshake_consume_initiation ::
 _wg_noise_handshake_create_initiation ::
 _wg_noise_set_static_identity_private_key :: _wg_noise_handshake_init ::
 _wg_noise_init :: _blake2s_final :: _blake2s_update ::
 _chacha20poly1305_decrypt :: _curve25519_generic :: _quickproof_free ::
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


