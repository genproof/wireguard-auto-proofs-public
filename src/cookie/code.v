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
  Definition source_file := "drivers/net/wireguard/cookie.c".
  Definition normalized := true.
End Info.

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
Definition ___crypto_memneq : ident := $"__crypto_memneq".
Definition ___gp_atomic64_t : ident := $"__gp_atomic64_t".
Definition ___gp_spinlock_t : ident := $"__gp_spinlock_t".
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _blake : ident := $"blake".
Definition _blake2s : ident := $"blake2s".
Definition _blake2s_ctx : ident := $"blake2s_ctx".
Definition _blake2s_final : ident := $"blake2s_final".
Definition _blake2s_init : ident := $"blake2s_init".
Definition _blake2s_init_key : ident := $"blake2s_init_key".
Definition _blake2s_update : ident := $"blake2s_update".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _chaining_key : ident := $"chaining_key".
Definition _check_cookie : ident := $"check_cookie".
Definition _checker : ident := $"checker".
Definition _compute_mac1 : ident := $"compute_mac1".
Definition _compute_mac2 : ident := $"compute_mac2".
Definition _computed_mac : ident := $"computed_mac".
Definition _cookie : ident := $"cookie".
Definition _cookie__1 : ident := $"cookie__1".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _cookie_key_label : ident := $"cookie_key_label".
Definition _counter : ident := $"counter".
Definition _crypto_memneq : ident := $"crypto_memneq".
Definition _ctx : ident := $"ctx".
Definition _current_keypair : ident := $"current_keypair".
Definition _data : ident := $"data".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _dst : ident := $"dst".
Definition _encrypted_cookie : ident := $"encrypted_cookie".
Definition _entry : ident := $"entry".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _f : ident := $"f".
Definition _get_random_bytes : ident := $"get_random_bytes".
Definition _get_random_bytes_wait : ident := $"get_random_bytes_wait".
Definition _h : ident := $"h".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _header : ident := $"header".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _in : ident := $"in".
Definition _in6_addr : ident := $"in6_addr".
Definition _in_addr : ident := $"in_addr".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _inlen : ident := $"inlen".
Definition _internal_id : ident := $"internal_id".
Definition _ip4 : ident := $"ip4".
Definition _ip6 : ident := $"ip6".
Definition _iphdr : ident := $"iphdr".
Definition _ipv6hdr : ident := $"ipv6hdr".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _key : ident := $"key".
Definition _keylen : ident := $"keylen".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kref : ident := $"kref".
Definition _ktime_get_coarse_boottime_ns : ident := $"ktime_get_coarse_boottime_ns".
Definition _label : ident := $"label".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _len : ident := $"len".
Definition _lock : ident := $"lock".
Definition _mac1 : ident := $"mac1".
Definition _mac1_key_label : ident := $"mac1_key_label".
Definition _mac2 : ident := $"mac2".
Definition _macs : ident := $"macs".
Definition _main : ident := $"main".
Definition _make_cookie : ident := $"make_cookie".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _message : ident := $"message".
Definition _message_handshake_cookie : ident := $"message_handshake_cookie".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _message_macs : ident := $"message_macs".
Definition _net : ident := $"net".
Definition _net_device : ident := $"net_device".
Definition _next : ident := $"next".
Definition _next_keypair : ident := $"next_keypair".
Definition _noise_handshake : ident := $"noise_handshake".
Definition _noise_keypair : ident := $"noise_keypair".
Definition _noise_keypairs : ident := $"noise_keypairs".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _noise_static_identity : ident := $"noise_static_identity".
Definition _noise_symmetric_key : ident := $"noise_symmetric_key".
Definition _nonce : ident := $"nonce".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _peer : ident := $"peer".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _precompute_key : ident := $"precompute_key".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _protocol : ident := $"protocol".
Definition _pubkey : ident := $"pubkey".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _quickproof_swab16 : ident := $"quickproof_swab16".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiver_index : ident := $"receiver_index".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
Definition _ret : ident := $"ret".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s6_addr : ident := $"s6_addr".
Definition _s_addr : ident := $"s_addr".
Definition _saddr : ident := $"saddr".
Definition _secret : ident := $"secret".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _size : ident := $"size".
Definition _sk_buff : ident := $"sk_buff".
Definition _skb : ident := $"skb".
Definition _source : ident := $"source".
Definition _src : ident := $"src".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _t : ident := $"t".
Definition _type : ident := $"type".
Definition _udp : ident := $"udp".
Definition _udphdr : ident := $"udphdr".
Definition _unused : ident := $"unused".
Definition _wg : ident := $"wg".
Definition _wg_birthdate_has_expired : ident := $"wg_birthdate_has_expired".
Definition _wg_cookie_add_mac_to_packet : ident := $"wg_cookie_add_mac_to_packet".
Definition _wg_cookie_checker_init : ident := $"wg_cookie_checker_init".
Definition _wg_cookie_checker_precompute_device_keys : ident := $"wg_cookie_checker_precompute_device_keys".
Definition _wg_cookie_checker_precompute_peer_keys : ident := $"wg_cookie_checker_precompute_peer_keys".
Definition _wg_cookie_init : ident := $"wg_cookie_init".
Definition _wg_cookie_message_consume : ident := $"wg_cookie_message_consume".
Definition _wg_cookie_message_create : ident := $"wg_cookie_message_create".
Definition _wg_cookie_validate_packet : ident := $"wg_cookie_validate_packet".
Definition _wg_device : ident := $"wg_device".
Definition _wg_index_hashtable_lookup : ident := $"wg_index_hashtable_lookup".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_peer_put : ident := $"wg_peer_put".
Definition _wg_ratelimiter_allow : ident := $"wg_ratelimiter_allow".
Definition _x : ident := $"x".
Definition _xchacha20poly1305_decrypt : ident := $"xchacha20poly1305_decrypt".
Definition _xchacha20poly1305_encrypt : ident := $"xchacha20poly1305_encrypt".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition f_blake2s_init_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ctx, (tptr (Tstruct _blake2s_ctx noattr))) ::
                (_outlen, tulong) :: (_key, (tptr tvoid)) ::
                (_keylen, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Econst_int (Int.repr 0) tint))
  (Scall None
    (Evar ___blake2s_init (Tfunction
                            ((tptr (Tstruct _blake2s_ctx noattr)) ::
                             tulong :: (tptr tvoid) :: tulong :: nil) tvoid
                            cc_default))
    ((Etempvar _ctx (tptr (Tstruct _blake2s_ctx noattr))) ::
     (Etempvar _outlen tulong) :: (Etempvar _key (tptr tvoid)) ::
     (Etempvar _keylen tulong) :: nil)))
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

Definition f_crypto_memneq := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tvoid)) :: (_b, (tptr tvoid)) ::
                (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tint) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar ___crypto_memneq (Tfunction
                               ((tptr tvoid) :: (tptr tvoid) :: tulong ::
                                nil) tulong cc_default))
      ((Etempvar _a (tptr tvoid)) :: (Etempvar _b (tptr tvoid)) ::
       (Etempvar _size tulong) :: nil))
    (Sifthenelse (Ebinop One (Etempvar _t'1 tulong)
                   (Econst_long (Int64.repr 0) tulong) tint)
      (Sset _t'2 (Ecast (Econst_int (Int.repr 1) tint) tint))
      (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tint))))
  (Sreturn (Some (Etempvar _t'2 tint))))
|}.

Definition f_wg_cookie_checker_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_checker, (tptr (Tstruct _cookie_checker noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _ktime_get_coarse_boottime_ns (Tfunction nil tulong cc_default))
      nil)
    (Sassign
      (Efield
        (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
          (Tstruct _cookie_checker noattr)) _secret_birthdate tulong)
      (Etempvar _t'1 tulong)))
  (Ssequence
    (Scall None
      (Evar _get_random_bytes (Tfunction ((tptr tvoid) :: tulong :: nil)
                                tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
           (Tstruct _cookie_checker noattr)) _secret (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Sassign
      (Efield
        (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
          (Tstruct _cookie_checker noattr)) _device
        (tptr (Tstruct _wg_device noattr)))
      (Etempvar _wg (tptr (Tstruct _wg_device noattr))))))
|}.

Definition v_mac1_key_label := {|
  gvar_info := (tarray tuchar 8);
  gvar_init := (Init_int8 (Int.repr 109) :: Init_int8 (Int.repr 97) ::
                Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 49) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition v_cookie_key_label := {|
  gvar_info := (tarray tuchar 8);
  gvar_init := (Init_int8 (Int.repr 99) :: Init_int8 (Int.repr 111) ::
                Init_int8 (Int.repr 111) :: Init_int8 (Int.repr 107) ::
                Init_int8 (Int.repr 105) :: Init_int8 (Int.repr 101) ::
                Init_int8 (Int.repr 45) :: Init_int8 (Int.repr 45) :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f_precompute_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_key, (tptr tuchar)) :: (_pubkey, (tptr tuchar)) ::
                (_label, (tptr tuchar)) :: nil);
  fn_vars := ((_blake, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _blake2s_init (Tfunction
                          ((tptr (Tstruct _blake2s_ctx noattr)) :: tulong ::
                           nil) tvoid cc_default))
    ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
       (tptr (Tstruct _blake2s_ctx noattr))) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _blake2s_update (Tfunction
                              ((tptr (Tstruct _blake2s_ctx noattr)) ::
                               (tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
      ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
         (tptr (Tstruct _blake2s_ctx noattr))) ::
       (Etempvar _label (tptr tuchar)) :: (Econst_int (Int.repr 8) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _blake2s_update (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
        ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _pubkey (tptr tuchar)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Scall None
        (Evar _blake2s_final (Tfunction
                               ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                (tptr tuchar) :: nil) tvoid cc_default))
        ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _key (tptr tuchar)) :: nil)))))
|}.

Definition f_wg_cookie_checker_precompute_device_keys := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_checker, (tptr (Tstruct _cookie_checker noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'4, (tptr (Tstruct _wg_device noattr))) ::
               (_t'3, (tptr (Tstruct _wg_device noattr))) :: (_t'2, tbool) ::
               (_t'1, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1
    (Efield
      (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
        (Tstruct _cookie_checker noattr)) _device
      (tptr (Tstruct _wg_device noattr))))
  (Ssequence
    (Sset _t'2
      (Efield
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _wg_device noattr)))
            (Tstruct _wg_device noattr)) _static_identity
          (Tstruct _noise_static_identity noattr)) _has_identity tbool))
    (Sifthenelse (Etempvar _t'2 tbool)
      (Ssequence
        (Ssequence
          (Sset _t'4
            (Efield
              (Ederef
                (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                (Tstruct _cookie_checker noattr)) _device
              (tptr (Tstruct _wg_device noattr))))
          (Scall None
            (Evar _precompute_key (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     (tptr tuchar) :: nil) tvoid cc_default))
            ((Efield
               (Ederef
                 (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                 (Tstruct _cookie_checker noattr)) _cookie_encryption_key
               (tarray tuchar 32)) ::
             (Efield
               (Efield
                 (Ederef (Etempvar _t'4 (tptr (Tstruct _wg_device noattr)))
                   (Tstruct _wg_device noattr)) _static_identity
                 (Tstruct _noise_static_identity noattr)) _static_public
               (tarray tuchar 32)) ::
             (Evar _cookie_key_label (tarray tuchar 8)) :: nil)))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef
                (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                (Tstruct _cookie_checker noattr)) _device
              (tptr (Tstruct _wg_device noattr))))
          (Scall None
            (Evar _precompute_key (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     (tptr tuchar) :: nil) tvoid cc_default))
            ((Efield
               (Ederef
                 (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                 (Tstruct _cookie_checker noattr)) _message_mac1_key
               (tarray tuchar 32)) ::
             (Efield
               (Efield
                 (Ederef (Etempvar _t'3 (tptr (Tstruct _wg_device noattr)))
                   (Tstruct _wg_device noattr)) _static_identity
                 (Tstruct _noise_static_identity noattr)) _static_public
               (tarray tuchar 32)) ::
             (Evar _mac1_key_label (tarray tuchar 8)) :: nil))))
      (Ssequence
        (Scall None
          (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                          (tptr tvoid) cc_default))
          ((Efield
             (Ederef
               (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
               (Tstruct _cookie_checker noattr)) _cookie_encryption_key
             (tarray tuchar 32)) :: (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Scall None
          (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                          (tptr tvoid) cc_default))
          ((Efield
             (Ederef
               (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
               (Tstruct _cookie_checker noattr)) _message_mac1_key
             (tarray tuchar 32)) :: (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 32) tint) :: nil))))))
|}.

Definition f_wg_cookie_checker_precompute_peer_keys := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _precompute_key (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) ::
                             (tptr tuchar) :: nil) tvoid cc_default))
    ((Efield
       (Efield
         (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
           (Tstruct _wg_peer noattr)) _latest_cookie
         (Tstruct _cookie noattr)) _cookie_decryption_key (tarray tuchar 32)) ::
     (Efield
       (Efield
         (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
           (Tstruct _wg_peer noattr)) _handshake
         (Tstruct _noise_handshake noattr)) _remote_static
       (tarray tuchar 32)) :: (Evar _cookie_key_label (tarray tuchar 8)) ::
     nil))
  (Scall None
    (Evar _precompute_key (Tfunction
                            ((tptr tuchar) :: (tptr tuchar) ::
                             (tptr tuchar) :: nil) tvoid cc_default))
    ((Efield
       (Efield
         (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
           (Tstruct _wg_peer noattr)) _latest_cookie
         (Tstruct _cookie noattr)) _message_mac1_key (tarray tuchar 32)) ::
     (Efield
       (Efield
         (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
           (Tstruct _wg_peer noattr)) _handshake
         (Tstruct _noise_handshake noattr)) _remote_static
       (tarray tuchar 32)) :: (Evar _mac1_key_label (tarray tuchar 8)) ::
     nil)))
|}.

Definition f_wg_cookie_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cookie__1, (tptr (Tstruct _cookie noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                  (tptr tvoid) cc_default))
  ((Etempvar _cookie__1 (tptr (Tstruct _cookie noattr))) ::
   (Econst_int (Int.repr 0) tint) ::
   (Esizeof (Tstruct _cookie noattr) tulong) :: nil))
|}.

Definition f_compute_mac1 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mac1, (tptr tuchar)) :: (_message, (tptr tvoid)) ::
                (_len, tulong) :: (_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _len
    (Ebinop Oadd
      (Ebinop Osub (Etempvar _len tulong)
        (Esizeof (Tstruct _message_macs noattr) tulong) tulong)
      (Econst_long (Int64.repr 0) tulong) tulong))
  (Scall None
    (Evar _blake2s (Tfunction
                     ((tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
                      (tptr tuchar) :: tulong :: nil) tvoid cc_default))
    ((Etempvar _key (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
     (Etempvar _message (tptr tvoid)) :: (Etempvar _len tulong) ::
     (Etempvar _mac1 (tptr tuchar)) :: (Econst_int (Int.repr 16) tint) ::
     nil)))
|}.

Definition f_compute_mac2 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_mac2, (tptr tuchar)) :: (_message, (tptr tvoid)) ::
                (_len, tulong) :: (_cookie__1, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sset _len
    (Ebinop Oadd
      (Ebinop Osub (Etempvar _len tulong)
        (Esizeof (Tstruct _message_macs noattr) tulong) tulong)
      (Econst_long (Int64.repr 16) tulong) tulong))
  (Scall None
    (Evar _blake2s (Tfunction
                     ((tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
                      (tptr tuchar) :: tulong :: nil) tvoid cc_default))
    ((Etempvar _cookie__1 (tptr tuchar)) ::
     (Econst_int (Int.repr 16) tint) :: (Etempvar _message (tptr tvoid)) ::
     (Etempvar _len tulong) :: (Etempvar _mac2 (tptr tuchar)) ::
     (Econst_int (Int.repr 16) tint) :: nil)))
|}.

Definition f_make_cookie := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_cookie__1, (tptr tuchar)) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) ::
                (_checker, (tptr (Tstruct _cookie_checker noattr))) :: nil);
  fn_vars := ((_blake, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := ((_t'4, tushort) :: (_t'3, tushort) :: (_t'2, tbool) ::
               (_t'1, tulong) :: (_t'7, tulong) :: (_t'6, tushort) ::
               (_t'5, tushort) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Ssequence
      (Sset _t'7
        (Efield
          (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
            (Tstruct _cookie_checker noattr)) _secret_birthdate tulong))
      (Scall (Some _t'2)
        (Evar _wg_birthdate_has_expired (Tfunction (tulong :: tulong :: nil)
                                          tbool cc_default))
        ((Etempvar _t'7 tulong) :: (Econst_int (Int.repr 120) tint) :: nil)))
    (Sifthenelse (Etempvar _t'2 tbool)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _ktime_get_coarse_boottime_ns (Tfunction nil tulong
                                                  cc_default)) nil)
          (Sassign
            (Efield
              (Ederef
                (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                (Tstruct _cookie_checker noattr)) _secret_birthdate tulong)
            (Etempvar _t'1 tulong)))
        (Scall None
          (Evar _get_random_bytes (Tfunction ((tptr tvoid) :: tulong :: nil)
                                    tvoid cc_default))
          ((Efield
             (Ederef
               (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
               (Tstruct _cookie_checker noattr)) _secret (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _blake2s_init_key (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 tulong :: (tptr tvoid) :: tulong :: nil)
                                tvoid cc_default))
      ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
         (tptr (Tstruct _blake2s_ctx noattr))) ::
       (Econst_int (Int.repr 16) tint) ::
       (Efield
         (Ederef (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
           (Tstruct _cookie_checker noattr)) _secret (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Ssequence
        (Scall (Some _t'4)
          (Evar _quickproof_swab16 (Tfunction (tushort :: nil) tushort
                                     cc_default))
          ((Ecast (Econst_int (Int.repr 2048) tint) tushort) :: nil))
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                (Tstruct _sk_buff noattr)) _protocol tushort))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tushort)
                         (Etempvar _t'4 tushort) tint)
            (Scall None
              (Evar _blake2s_update (Tfunction
                                      ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                       (tptr tuchar) :: tulong :: nil) tvoid
                                      cc_default))
              ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
                 (tptr (Tstruct _blake2s_ctx noattr))) ::
               (Ecast
                 (Eaddrof
                   (Efield
                     (Efield
                       (Ederef
                         (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                         (Tstruct _sk_buff noattr)) _ip4
                       (Tstruct _iphdr noattr)) _saddr
                     (Tstruct _in_addr noattr))
                   (tptr (Tstruct _in_addr noattr))) (tptr tuchar)) ::
               (Esizeof (Tstruct _in_addr noattr) tulong) :: nil))
            (Ssequence
              (Scall (Some _t'3)
                (Evar _quickproof_swab16 (Tfunction (tushort :: nil) tushort
                                           cc_default))
                ((Ecast (Econst_int (Int.repr 34525) tint) tushort) :: nil))
              (Ssequence
                (Sset _t'6
                  (Efield
                    (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                      (Tstruct _sk_buff noattr)) _protocol tushort))
                (Sifthenelse (Ebinop Oeq (Etempvar _t'6 tushort)
                               (Etempvar _t'3 tushort) tint)
                  (Scall None
                    (Evar _blake2s_update (Tfunction
                                            ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                    ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
                       (tptr (Tstruct _blake2s_ctx noattr))) ::
                     (Ecast
                       (Eaddrof
                         (Efield
                           (Efield
                             (Ederef
                               (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                               (Tstruct _sk_buff noattr)) _ip6
                             (Tstruct _ipv6hdr noattr)) _saddr
                           (Tstruct _in6_addr noattr))
                         (tptr (Tstruct _in6_addr noattr))) (tptr tuchar)) ::
                     (Esizeof (Tstruct _in6_addr noattr) tulong) :: nil))
                  Sskip))))))
      (Ssequence
        (Scall None
          (Evar _blake2s_update (Tfunction
                                  ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
          ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
             (tptr (Tstruct _blake2s_ctx noattr))) ::
           (Ecast
             (Eaddrof
               (Efield
                 (Efield
                   (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                     (Tstruct _sk_buff noattr)) _udp
                   (Tstruct _udphdr noattr)) _source (tarray tuchar 2))
               (tptr (tarray tuchar 2))) (tptr tuchar)) ::
           (Esizeof tushort tulong) :: nil))
        (Scall None
          (Evar _blake2s_final (Tfunction
                                 ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                  (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
             (tptr (Tstruct _blake2s_ctx noattr))) ::
           (Etempvar _cookie__1 (tptr tuchar)) :: nil))))))
|}.

Definition f_wg_cookie_validate_packet := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_checker, (tptr (Tstruct _cookie_checker noattr))) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) ::
                (_check_cookie, tbool) :: nil);
  fn_vars := ((_computed_mac, (tarray tuchar 16)) ::
              (_cookie__1, (tarray tuchar 16)) :: nil);
  fn_temps := ((_macs, (tptr (Tstruct _message_macs noattr))) ::
               (_ret, tint) :: (_t'3, tbool) :: (_t'2, tint) ::
               (_t'1, tint) :: (_t'9, tuint) :: (_t'8, (tptr tuchar)) ::
               (_t'7, tuint) :: (_t'6, (tptr tuchar)) :: (_t'5, tuint) ::
               (_t'4, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'8
      (Efield
        (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
          (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
    (Ssequence
      (Sset _t'9
        (Efield
          (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
            (Tstruct _sk_buff noattr)) _len tuint))
      (Sset _macs
        (Ecast
          (Ebinop Osub
            (Ebinop Oadd (Etempvar _t'8 (tptr tuchar)) (Etempvar _t'9 tuint)
              (tptr tuchar)) (Esizeof (Tstruct _message_macs noattr) tulong)
            (tptr tuchar)) (tptr (Tstruct _message_macs noattr))))))
  (Ssequence
    (Sloop
      (Ssequence
        (Sset _ret (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _t'6
              (Efield
                (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                  (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
            (Ssequence
              (Sset _t'7
                (Efield
                  (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                    (Tstruct _sk_buff noattr)) _len tuint))
              (Scall None
                (Evar _compute_mac1 (Tfunction
                                      ((tptr tuchar) :: (tptr tvoid) ::
                                       tulong :: (tptr tuchar) :: nil) tvoid
                                      cc_default))
                ((Evar _computed_mac (tarray tuchar 16)) ::
                 (Etempvar _t'6 (tptr tuchar)) :: (Etempvar _t'7 tuint) ::
                 (Efield
                   (Ederef
                     (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                     (Tstruct _cookie_checker noattr)) _message_mac1_key
                   (tarray tuchar 32)) :: nil))))
          (Ssequence
            (Ssequence
              (Scall (Some _t'1)
                (Evar _crypto_memneq (Tfunction
                                       ((tptr tvoid) :: (tptr tvoid) ::
                                        tulong :: nil) tint cc_default))
                ((Evar _computed_mac (tarray tuchar 16)) ::
                 (Efield
                   (Ederef
                     (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
                     (Tstruct _message_macs noattr)) _mac1
                   (tarray tuchar 16)) :: (Econst_int (Int.repr 16) tint) ::
                 nil))
              (Sifthenelse (Etempvar _t'1 tint) Sbreak Sskip))
            (Ssequence
              (Sset _ret (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Sifthenelse (Eunop Onotbool (Etempvar _check_cookie tbool)
                               tint)
                  Sbreak
                  Sskip)
                (Ssequence
                  (Scall None
                    (Evar _make_cookie (Tfunction
                                         ((tptr tuchar) ::
                                          (tptr (Tstruct _sk_buff noattr)) ::
                                          (tptr (Tstruct _cookie_checker noattr)) ::
                                          nil) tvoid cc_default))
                    ((Evar _cookie__1 (tarray tuchar 16)) ::
                     (Etempvar _skb (tptr (Tstruct _sk_buff noattr))) ::
                     (Etempvar _checker (tptr (Tstruct _cookie_checker noattr))) ::
                     nil))
                  (Ssequence
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                            (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
                      (Ssequence
                        (Sset _t'5
                          (Efield
                            (Ederef
                              (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
                              (Tstruct _sk_buff noattr)) _len tuint))
                        (Scall None
                          (Evar _compute_mac2 (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tvoid) :: tulong ::
                                                 (tptr tuchar) :: nil) tvoid
                                                cc_default))
                          ((Evar _computed_mac (tarray tuchar 16)) ::
                           (Etempvar _t'4 (tptr tuchar)) ::
                           (Etempvar _t'5 tuint) ::
                           (Evar _cookie__1 (tarray tuchar 16)) :: nil))))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'2)
                          (Evar _crypto_memneq (Tfunction
                                                 ((tptr tvoid) ::
                                                  (tptr tvoid) :: tulong ::
                                                  nil) tint cc_default))
                          ((Evar _computed_mac (tarray tuchar 16)) ::
                           (Efield
                             (Ederef
                               (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
                               (Tstruct _message_macs noattr)) _mac2
                             (tarray tuchar 16)) ::
                           (Econst_int (Int.repr 16) tint) :: nil))
                        (Sifthenelse (Etempvar _t'2 tint) Sbreak Sskip))
                      (Ssequence
                        (Sset _ret (Econst_int (Int.repr 2) tint))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'3)
                              (Evar _wg_ratelimiter_allow (Tfunction
                                                            ((tptr (Tstruct _sk_buff noattr)) ::
                                                             (tptr (Tstruct _net noattr)) ::
                                                             nil) tbool
                                                            cc_default))
                              ((Etempvar _skb (tptr (Tstruct _sk_buff noattr))) ::
                               (Ecast (Econst_int (Int.repr 0) tint)
                                 (tptr (Tstruct _net noattr))) :: nil))
                            (Sifthenelse (Eunop Onotbool
                                           (Etempvar _t'3 tbool) tint)
                              Sbreak
                              Sskip))
                          (Sset _ret (Econst_int (Int.repr 3) tint))))))))))))
      Sbreak)
    (Sreturn (Some (Etempvar _ret tint)))))
|}.

Definition f_wg_cookie_add_mac_to_packet := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_message, (tptr tvoid)) :: (_len, tulong) ::
                (_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_macs, (tptr (Tstruct _message_macs noattr))) ::
               (_t'2, tbool) :: (_t'1, tint) :: (_t'4, tulong) ::
               (_t'3, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _macs
    (Ecast
      (Ebinop Osub
        (Ebinop Oadd (Ecast (Etempvar _message (tptr tvoid)) (tptr tuchar))
          (Etempvar _len tulong) (tptr tuchar))
        (Esizeof (Tstruct _message_macs noattr) tulong) (tptr tuchar))
      (tptr (Tstruct _message_macs noattr))))
  (Ssequence
    (Scall None
      (Evar _compute_mac1 (Tfunction
                            ((tptr tuchar) :: (tptr tvoid) :: tulong ::
                             (tptr tuchar) :: nil) tvoid cc_default))
      ((Efield
         (Ederef (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
           (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
       (Etempvar _message (tptr tvoid)) :: (Etempvar _len tulong) ::
       (Efield
         (Efield
           (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
             (Tstruct _wg_peer noattr)) _latest_cookie
           (Tstruct _cookie noattr)) _message_mac1_key (tarray tuchar 32)) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _memcpy (Tfunction
                        ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                        (tptr tvoid) cc_default))
        ((Efield
           (Efield
             (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
               (Tstruct _wg_peer noattr)) _latest_cookie
             (Tstruct _cookie noattr)) _last_mac1_sent (tarray tuchar 16)) ::
         (Efield
           (Ederef (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
             (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
         (Econst_int (Int.repr 16) tint) :: nil))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _latest_cookie
              (Tstruct _cookie noattr)) _have_sent_mac1 tbool)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Efield
                  (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _latest_cookie
                  (Tstruct _cookie noattr)) _is_valid tbool))
            (Sifthenelse (Etempvar _t'3 tbool)
              (Ssequence
                (Ssequence
                  (Sset _t'4
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                          (Tstruct _wg_peer noattr)) _latest_cookie
                        (Tstruct _cookie noattr)) _birthdate tulong))
                  (Scall (Some _t'2)
                    (Evar _wg_birthdate_has_expired (Tfunction
                                                      (tulong :: tulong ::
                                                       nil) tbool cc_default))
                    ((Etempvar _t'4 tulong) ::
                     (Ebinop Osub (Econst_int (Int.repr 120) tint)
                       (Econst_int (Int.repr 5) tint) tint) :: nil)))
                (Sset _t'1
                  (Ecast (Eunop Onotbool (Etempvar _t'2 tbool) tint) tbool)))
              (Sset _t'1 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'1 tint)
            (Scall None
              (Evar _compute_mac2 (Tfunction
                                    ((tptr tuchar) :: (tptr tvoid) ::
                                     tulong :: (tptr tuchar) :: nil) tvoid
                                    cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Etempvar _message (tptr tvoid)) :: (Etempvar _len tulong) ::
               (Efield
                 (Efield
                   (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _latest_cookie
                   (Tstruct _cookie noattr)) _cookie (tarray tuchar 16)) ::
               nil))
            (Scall None
              (Evar _memset (Tfunction
                              ((tptr tvoid) :: tint :: tulong :: nil)
                              (tptr tvoid) cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
                   (Tstruct _message_macs noattr)) _mac2 (tarray tuchar 16)) ::
               (Econst_int (Int.repr 0) tint) ::
               (Econst_int (Int.repr 16) tint) :: nil))))))))
|}.

Definition f_wg_cookie_message_create := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _message_handshake_cookie noattr))) ::
                (_skb, (tptr (Tstruct _sk_buff noattr))) ::
                (_index, tuint) ::
                (_checker, (tptr (Tstruct _cookie_checker noattr))) :: nil);
  fn_vars := ((_cookie__1, (tarray tuchar 16)) :: nil);
  fn_temps := ((_macs, (tptr (Tstruct _message_macs noattr))) ::
               (_t'2, tuint) :: (_t'1, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
          (Tstruct _sk_buff noattr)) _data (tptr tuchar)))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _skb (tptr (Tstruct _sk_buff noattr)))
            (Tstruct _sk_buff noattr)) _len tuint))
      (Sset _macs
        (Ecast
          (Ebinop Osub
            (Ebinop Oadd (Ecast (Etempvar _t'1 (tptr tuchar)) (tptr tuchar))
              (Etempvar _t'2 tuint) (tptr tuchar))
            (Esizeof (Tstruct _message_macs noattr) tulong) (tptr tuchar))
          (tptr (Tstruct _message_macs noattr))))))
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Ederef
            (Etempvar _dst (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _header
          (Tstruct _message_header noattr)) _type tuint)
      (Ecast (Econst_int (Int.repr 3) tint) tuint))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Etempvar _dst (tptr (Tstruct _message_handshake_cookie noattr)))
            (Tstruct _message_handshake_cookie noattr)) _receiver_index
          tuint) (Etempvar _index tuint))
      (Ssequence
        (Scall None
          (Evar _get_random_bytes_wait (Tfunction
                                         ((tptr tvoid) :: tulong :: nil)
                                         tvoid cc_default))
          ((Efield
             (Ederef
               (Etempvar _dst (tptr (Tstruct _message_handshake_cookie noattr)))
               (Tstruct _message_handshake_cookie noattr)) _nonce
             (tarray tuchar 24)) :: (Econst_int (Int.repr 24) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _make_cookie (Tfunction
                                 ((tptr tuchar) ::
                                  (tptr (Tstruct _sk_buff noattr)) ::
                                  (tptr (Tstruct _cookie_checker noattr)) ::
                                  nil) tvoid cc_default))
            ((Evar _cookie__1 (tarray tuchar 16)) ::
             (Etempvar _skb (tptr (Tstruct _sk_buff noattr))) ::
             (Etempvar _checker (tptr (Tstruct _cookie_checker noattr))) ::
             nil))
          (Scall None
            (Evar _xchacha20poly1305_encrypt (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) :: nil) tvoid
                                               cc_default))
            ((Efield
               (Ederef
                 (Etempvar _dst (tptr (Tstruct _message_handshake_cookie noattr)))
                 (Tstruct _message_handshake_cookie noattr))
               _encrypted_cookie (tarray tuchar 32)) ::
             (Evar _cookie__1 (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) ::
             (Efield
               (Ederef (Etempvar _macs (tptr (Tstruct _message_macs noattr)))
                 (Tstruct _message_macs noattr)) _mac1 (tarray tuchar 16)) ::
             (Econst_int (Int.repr 16) tint) ::
             (Efield
               (Ederef
                 (Etempvar _dst (tptr (Tstruct _message_handshake_cookie noattr)))
                 (Tstruct _message_handshake_cookie noattr)) _nonce
               (tarray tuchar 24)) ::
             (Efield
               (Ederef
                 (Etempvar _checker (tptr (Tstruct _cookie_checker noattr)))
                 (Tstruct _cookie_checker noattr)) _cookie_encryption_key
               (tarray tuchar 32)) :: nil)))))))
|}.

Definition f_wg_cookie_message_consume := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr (Tstruct _message_handshake_cookie noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := ((_peer, (tptr (Tstruct _wg_peer noattr))) ::
              (_cookie__1, (tarray tuchar 16)) :: nil);
  fn_temps := ((_ret, tbool) :: (_t'3, tulong) :: (_t'2, tbool) ::
               (_t'1, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'14, tuint) ::
               (_t'13, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'12, tbool) :: (_t'11, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'10, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'9, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'8, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'7, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'6, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'4, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Evar _peer (tptr (Tstruct _wg_peer noattr)))
    (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Ssequence
        (Sset _t'13
          (Efield
            (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
              (Tstruct _wg_device noattr)) _index_hashtable
            (tptr (Tstruct _index_hashtable noattr))))
        (Ssequence
          (Sset _t'14
            (Efield
              (Ederef
                (Etempvar _src (tptr (Tstruct _message_handshake_cookie noattr)))
                (Tstruct _message_handshake_cookie noattr)) _receiver_index
              tuint))
          (Scall (Some _t'1)
            (Evar _wg_index_hashtable_lookup (Tfunction
                                               ((tptr (Tstruct _index_hashtable noattr)) ::
                                                tint :: tuint ::
                                                (tptr (tptr (Tstruct _wg_peer noattr))) ::
                                                nil)
                                               (tptr (Tstruct _index_hashtable_entry noattr))
                                               cc_default))
            ((Etempvar _t'13 (tptr (Tstruct _index_hashtable noattr))) ::
             (Ebinop Oor (Econst_int (Int.repr 1) tint)
               (Econst_int (Int.repr 2) tint) tint) ::
             (Etempvar _t'14 tuint) ::
             (Eaddrof (Evar _peer (tptr (Tstruct _wg_peer noattr)))
               (tptr (tptr (Tstruct _wg_peer noattr)))) :: nil))))
      (Sifthenelse (Eunop Onotbool
                     (Etempvar _t'1 (tptr (Tstruct _index_hashtable_entry noattr)))
                     tint)
        (Sreturn None)
        Sskip))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'11 (Evar _peer (tptr (Tstruct _wg_peer noattr))))
            (Ssequence
              (Sset _t'12
                (Efield
                  (Efield
                    (Ederef (Etempvar _t'11 (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _latest_cookie
                    (Tstruct _cookie noattr)) _have_sent_mac1 tbool))
              (Sifthenelse (Eunop Onotbool (Etempvar _t'12 tbool) tint)
                Sbreak
                Sskip)))
          (Ssequence
            (Ssequence
              (Ssequence
                (Sset _t'9 (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                (Ssequence
                  (Sset _t'10 (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                  (Scall (Some _t'2)
                    (Evar _xchacha20poly1305_decrypt (Tfunction
                                                       ((tptr tuchar) ::
                                                        (tptr tuchar) ::
                                                        tulong ::
                                                        (tptr tuchar) ::
                                                        tulong ::
                                                        (tptr tuchar) ::
                                                        (tptr tuchar) :: nil)
                                                       tbool cc_default))
                    ((Evar _cookie__1 (tarray tuchar 16)) ::
                     (Efield
                       (Ederef
                         (Etempvar _src (tptr (Tstruct _message_handshake_cookie noattr)))
                         (Tstruct _message_handshake_cookie noattr))
                       _encrypted_cookie (tarray tuchar 32)) ::
                     (Esizeof (tarray tuchar 32) tulong) ::
                     (Efield
                       (Efield
                         (Ederef
                           (Etempvar _t'9 (tptr (Tstruct _wg_peer noattr)))
                           (Tstruct _wg_peer noattr)) _latest_cookie
                         (Tstruct _cookie noattr)) _last_mac1_sent
                       (tarray tuchar 16)) ::
                     (Econst_int (Int.repr 16) tint) ::
                     (Efield
                       (Ederef
                         (Etempvar _src (tptr (Tstruct _message_handshake_cookie noattr)))
                         (Tstruct _message_handshake_cookie noattr)) _nonce
                       (tarray tuchar 24)) ::
                     (Efield
                       (Efield
                         (Ederef
                           (Etempvar _t'10 (tptr (Tstruct _wg_peer noattr)))
                           (Tstruct _wg_peer noattr)) _latest_cookie
                         (Tstruct _cookie noattr)) _cookie_decryption_key
                       (tarray tuchar 32)) :: nil))))
              (Sset _ret (Ecast (Etempvar _t'2 tbool) tbool)))
            (Sifthenelse (Etempvar _ret tbool)
              (Ssequence
                (Ssequence
                  (Sset _t'8 (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                  (Scall None
                    (Evar _memcpy (Tfunction
                                    ((tptr tvoid) :: (tptr tvoid) ::
                                     tulong :: nil) (tptr tvoid) cc_default))
                    ((Efield
                       (Efield
                         (Ederef
                           (Etempvar _t'8 (tptr (Tstruct _wg_peer noattr)))
                           (Tstruct _wg_peer noattr)) _latest_cookie
                         (Tstruct _cookie noattr)) _cookie
                       (tarray tuchar 16)) ::
                     (Evar _cookie__1 (tarray tuchar 16)) ::
                     (Econst_int (Int.repr 16) tint) :: nil)))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _ktime_get_coarse_boottime_ns (Tfunction nil
                                                            tulong
                                                            cc_default)) nil)
                    (Ssequence
                      (Sset _t'7
                        (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _t'7 (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _latest_cookie
                            (Tstruct _cookie noattr)) _birthdate tulong)
                        (Etempvar _t'3 tulong))))
                  (Ssequence
                    (Ssequence
                      (Sset _t'6
                        (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _t'6 (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _latest_cookie
                            (Tstruct _cookie noattr)) _is_valid tbool)
                        (Econst_int (Int.repr 1) tint)))
                    (Ssequence
                      (Sset _t'5
                        (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _latest_cookie
                            (Tstruct _cookie noattr)) _have_sent_mac1 tbool)
                        (Econst_int (Int.repr 0) tint))))))
              Sskip)))
        Sbreak)
      (Ssequence
        (Sset _t'4 (Evar _peer (tptr (Tstruct _wg_peer noattr))))
        (Scall None
          (Evar _wg_peer_put (Tfunction
                               ((tptr (Tstruct _wg_peer noattr)) :: nil)
                               tvoid cc_default))
          ((Etempvar _t'4 (tptr (Tstruct _wg_peer noattr))) :: nil))))))
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
 Composite _net Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _sk_buff Struct
   (Member_plain _data (tptr tuchar) :: Member_plain _len tuint ::
    Member_plain _protocol tushort ::
    Member_plain _ip4 (Tstruct _iphdr noattr) ::
    Member_plain _ip6 (Tstruct _ipv6hdr noattr) ::
    Member_plain _udp (Tstruct _udphdr noattr) :: nil)
   noattr ::
 Composite _message_header Struct (Member_plain _type tuint :: nil) noattr ::
 Composite _message_macs Struct
   (Member_plain _mac1 (tarray tuchar 16) ::
    Member_plain _mac2 (tarray tuchar 16) :: nil)
   noattr ::
 Composite _message_handshake_cookie Struct
   (Member_plain _header (Tstruct _message_header noattr) ::
    Member_plain _receiver_index tuint ::
    Member_plain _nonce (tarray tuchar 24) ::
    Member_plain _encrypted_cookie (tarray tuchar 32) :: nil)
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
 (_quickproof_swab16, Gfun(Internal f_quickproof_swab16)) ::
 (_ktime_get_coarse_boottime_ns,
   Gfun(External (EF_external "ktime_get_coarse_boottime_ns"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_get_random_bytes,
   Gfun(External (EF_external "get_random_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tulong :: nil) tvoid
     cc_default)) ::
 (_get_random_bytes_wait,
   Gfun(External (EF_external "get_random_bytes_wait"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tulong :: nil) tvoid
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
 (_blake2s_init_key, Gfun(Internal f_blake2s_init_key)) ::
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
 (_wg_index_hashtable_lookup,
   Gfun(External (EF_external "wg_index_hashtable_lookup"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xptr :: nil)
                     AST.Xptr cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) :: tint :: tuint ::
      (tptr (tptr (Tstruct _wg_peer noattr))) :: nil)
     (tptr (Tstruct _index_hashtable_entry noattr)) cc_default)) ::
 (_wg_peer_put,
   Gfun(External (EF_external "wg_peer_put"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _wg_peer noattr)) :: nil) tvoid cc_default)) ::
 (_wg_ratelimiter_allow,
   Gfun(External (EF_external "wg_ratelimiter_allow"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default))
     ((tptr (Tstruct _sk_buff noattr)) :: (tptr (Tstruct _net noattr)) ::
      nil) tbool cc_default)) ::
 (_wg_birthdate_has_expired,
   Gfun(External (EF_external "wg_birthdate_has_expired"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xbool
                     cc_default)) (tulong :: tulong :: nil) tbool
     cc_default)) ::
 (___crypto_memneq,
   Gfun(External (EF_external "__crypto_memneq"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) tulong cc_default)) ::
 (_crypto_memneq, Gfun(Internal f_crypto_memneq)) ::
 (_wg_cookie_checker_init, Gfun(Internal f_wg_cookie_checker_init)) ::
 (_mac1_key_label, Gvar v_mac1_key_label) ::
 (_cookie_key_label, Gvar v_cookie_key_label) ::
 (_precompute_key, Gfun(Internal f_precompute_key)) ::
 (_wg_cookie_checker_precompute_device_keys, Gfun(Internal f_wg_cookie_checker_precompute_device_keys)) ::
 (_wg_cookie_checker_precompute_peer_keys, Gfun(Internal f_wg_cookie_checker_precompute_peer_keys)) ::
 (_wg_cookie_init, Gfun(Internal f_wg_cookie_init)) ::
 (_compute_mac1, Gfun(Internal f_compute_mac1)) ::
 (_compute_mac2, Gfun(Internal f_compute_mac2)) ::
 (_make_cookie, Gfun(Internal f_make_cookie)) ::
 (_wg_cookie_validate_packet, Gfun(Internal f_wg_cookie_validate_packet)) ::
 (_wg_cookie_add_mac_to_packet, Gfun(Internal f_wg_cookie_add_mac_to_packet)) ::
 (_wg_cookie_message_create, Gfun(Internal f_wg_cookie_message_create)) ::
 (_wg_cookie_message_consume, Gfun(Internal f_wg_cookie_message_consume)) ::
 nil).

Definition public_idents : list ident :=
(_wg_cookie_message_consume :: _wg_cookie_message_create ::
 _wg_cookie_add_mac_to_packet :: _wg_cookie_validate_packet ::
 _wg_cookie_init :: _wg_cookie_checker_precompute_peer_keys ::
 _wg_cookie_checker_precompute_device_keys :: _wg_cookie_checker_init ::
 ___crypto_memneq :: _wg_birthdate_has_expired :: _wg_ratelimiter_allow ::
 _wg_peer_put :: _wg_index_hashtable_lookup :: _blake2s_final ::
 _blake2s_update :: _xchacha20poly1305_decrypt ::
 _xchacha20poly1305_encrypt :: _get_random_bytes_wait :: _get_random_bytes ::
 _ktime_get_coarse_boottime_ns :: _memset :: _memcpy :: ___builtin_debug ::
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


