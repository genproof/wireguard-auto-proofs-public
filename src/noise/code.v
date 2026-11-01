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
  Definition source_file := "drivers/net/wireguard/noise.c".
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
Definition _add_new_keypair : ident := $"add_new_keypair".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _blake : ident := $"blake".
Definition _blake2s : ident := $"blake2s".
Definition _blake2s_ctx : ident := $"blake2s_ctx".
Definition _blake2s_final : ident := $"blake2s_final".
Definition _blake2s_init : ident := $"blake2s_init".
Definition _blake2s_update : ident := $"blake2s_update".
Definition _buf : ident := $"buf".
Definition _buflen : ident := $"buflen".
Definition _chacha20poly1305_decrypt : ident := $"chacha20poly1305_decrypt".
Definition _chacha20poly1305_encrypt : ident := $"chacha20poly1305_encrypt".
Definition _chaining_key : ident := $"chaining_key".
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _count : ident := $"count".
Definition _counter : ident := $"counter".
Definition _crypto_memneq : ident := $"crypto_memneq".
Definition _ctx : ident := $"ctx".
Definition _current_keypair : ident := $"current_keypair".
Definition _curve25519 : ident := $"curve25519".
Definition _curve25519_clamp_secret : ident := $"curve25519_clamp_secret".
Definition _curve25519_generate_public : ident := $"curve25519_generate_public".
Definition _curve25519_generate_secret : ident := $"curve25519_generate_secret".
Definition _data : ident := $"data".
Definition _data_len : ident := $"data_len".
Definition _derive_keys : ident := $"derive_keys".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _dh_calculation : ident := $"dh_calculation".
Definition _dst : ident := $"dst".
Definition _dst_ciphertext : ident := $"dst_ciphertext".
Definition _dst_plaintext : ident := $"dst_plaintext".
Definition _e : ident := $"e".
Definition _encrypted_nothing : ident := $"encrypted_nothing".
Definition _encrypted_static : ident := $"encrypted_static".
Definition _encrypted_timestamp : ident := $"encrypted_timestamp".
Definition _entry : ident := $"entry".
Definition _ephemeral_dst : ident := $"ephemeral_dst".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _ephemeral_src : ident := $"ephemeral_src".
Definition _f : ident := $"f".
Definition _first_dst : ident := $"first_dst".
Definition _first_len : ident := $"first_len".
Definition _flood_attack : ident := $"flood_attack".
Definition _get_random_bytes_wait : ident := $"get_random_bytes_wait".
Definition _h : ident := $"h".
Definition _handshake : ident := $"handshake".
Definition _handshake_init : ident := $"handshake_init".
Definition _handshake_init_chaining_key : ident := $"handshake_init_chaining_key".
Definition _handshake_init_hash : ident := $"handshake_init_hash".
Definition _handshake_name : ident := $"handshake_name".
Definition _handshake_ns : ident := $"handshake_ns".
Definition _handshake_zero : ident := $"handshake_zero".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _header : ident := $"header".
Definition _hmac : ident := $"hmac".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _i_hash : ident := $"i_hash".
Definition _identifier_name : ident := $"identifier_name".
Definition _in : ident := $"in".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _initiation_consumption : ident := $"initiation_consumption".
Definition _inlen : ident := $"inlen".
Definition _internal_id : ident := $"internal_id".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _kdf : ident := $"kdf".
Definition _key : ident := $"key".
Definition _key_is_new : ident := $"key_is_new".
Definition _keylen : ident := $"keylen".
Definition _keypair : ident := $"keypair".
Definition _keypair_counter : ident := $"keypair_counter".
Definition _keypair_create : ident := $"keypair_create".
Definition _keypair_free_kref : ident := $"keypair_free_kref".
Definition _keypair_free_rcu : ident := $"keypair_free_rcu".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kfree_sensitive : ident := $"kfree_sensitive".
Definition _kref : ident := $"kref".
Definition _kref__1 : ident := $"kref__1".
Definition _ktime_get_coarse_boottime_ns : ident := $"ktime_get_coarse_boottime_ns".
Definition _ktime_get_real_ts64 : ident := $"ktime_get_real_ts64".
Definition _kzalloc : ident := $"kzalloc".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _lock : ident := $"lock".
Definition _mac1 : ident := $"mac1".
Definition _mac2 : ident := $"mac2".
Definition _macs : ident := $"macs".
Definition _main : ident := $"main".
Definition _memcmp : ident := $"memcmp".
Definition _memcpy : ident := $"memcpy".
Definition _memset : ident := $"memset".
Definition _memzero_explicit : ident := $"memzero_explicit".
Definition _message_decrypt : ident := $"message_decrypt".
Definition _message_encrypt : ident := $"message_encrypt".
Definition _message_ephemeral : ident := $"message_ephemeral".
Definition _message_handshake_initiation : ident := $"message_handshake_initiation".
Definition _message_handshake_response : ident := $"message_handshake_response".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _message_macs : ident := $"message_macs".
Definition _mix_dh : ident := $"mix_dh".
Definition _mix_hash : ident := $"mix_hash".
Definition _mix_precomputed_dh : ident := $"mix_precomputed_dh".
Definition _mix_psk : ident := $"mix_psk".
Definition _n : ident := $"n".
Definition _net_device : ident := $"net_device".
Definition _new_keypair : ident := $"new_keypair".
Definition _next : ident := $"next".
Definition _next_keypair : ident := $"next_keypair".
Definition _noise_handshake : ident := $"noise_handshake".
Definition _noise_keypair : ident := $"noise_keypair".
Definition _noise_keypairs : ident := $"noise_keypairs".
Definition _noise_replay_counter : ident := $"noise_replay_counter".
Definition _noise_static_identity : ident := $"noise_static_identity".
Definition _noise_symmetric_key : ident := $"noise_symmetric_key".
Definition _now : ident := $"now".
Definition _old : ident := $"old".
Definition _old_keypair : ident := $"old_keypair".
Definition _out : ident := $"out".
Definition _outlen : ident := $"outlen".
Definition _output : ident := $"output".
Definition _p : ident := $"p".
Definition _peer : ident := $"peer".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _peer_preshared_key : ident := $"peer_preshared_key".
Definition _peer_public_key : ident := $"peer_public_key".
Definition _precomputed : ident := $"precomputed".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _private : ident := $"private".
Definition _private_key : ident := $"private_key".
Definition _psk : ident := $"psk".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _public : ident := $"public".
Definition _put_unaligned_be32 : ident := $"put_unaligned_be32".
Definition _put_unaligned_be64 : ident := $"put_unaligned_be64".
Definition _quickproof_rounddown_pow_of_two : ident := $"quickproof_rounddown_pow_of_two".
Definition _quickproof_success : ident := $"quickproof_success".
Definition _r : ident := $"r".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _received_keypair : ident := $"received_keypair".
Definition _receiver_index : ident := $"receiver_index".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
Definition _replay_attack : ident := $"replay_attack".
Definition _ret : ident := $"ret".
Definition _ret_peer : ident := $"ret_peer".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s : ident := $"s".
Definition _second_dst : ident := $"second_dst".
Definition _second_len : ident := $"second_len".
Definition _secret : ident := $"secret".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sender_index : ident := $"sender_index".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _size : ident := $"size".
Definition _src : ident := $"src".
Definition _src_ciphertext : ident := $"src_ciphertext".
Definition _src_len : ident := $"src_len".
Definition _src_plaintext : ident := $"src_plaintext".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _t : ident := $"t".
Definition _tai64n_now : ident := $"tai64n_now".
Definition _temp_hash : ident := $"temp_hash".
Definition _third_dst : ident := $"third_dst".
Definition _third_len : ident := $"third_len".
Definition _timespec64 : ident := $"timespec64".
Definition _timestamp : ident := $"timestamp".
Definition _tv_nsec : ident := $"tv_nsec".
Definition _tv_sec : ident := $"tv_sec".
Definition _type : ident := $"type".
Definition _unencrypted_ephemeral : ident := $"unencrypted_ephemeral".
Definition _unreference_now : ident := $"unreference_now".
Definition _unused : ident := $"unused".
Definition _v : ident := $"v".
Definition _wg : ident := $"wg".
Definition _wg_device : ident := $"wg_device".
Definition _wg_index_hashtable_insert : ident := $"wg_index_hashtable_insert".
Definition _wg_index_hashtable_lookup : ident := $"wg_index_hashtable_lookup".
Definition _wg_index_hashtable_remove : ident := $"wg_index_hashtable_remove".
Definition _wg_index_hashtable_replace : ident := $"wg_index_hashtable_replace".
Definition _wg_noise_expire_current_peer_keypairs : ident := $"wg_noise_expire_current_peer_keypairs".
Definition _wg_noise_handshake_begin_session : ident := $"wg_noise_handshake_begin_session".
Definition _wg_noise_handshake_clear : ident := $"wg_noise_handshake_clear".
Definition _wg_noise_handshake_consume_initiation : ident := $"wg_noise_handshake_consume_initiation".
Definition _wg_noise_handshake_consume_response : ident := $"wg_noise_handshake_consume_response".
Definition _wg_noise_handshake_create_initiation : ident := $"wg_noise_handshake_create_initiation".
Definition _wg_noise_handshake_create_response : ident := $"wg_noise_handshake_create_response".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_init : ident := $"wg_noise_init".
Definition _wg_noise_keypair_get : ident := $"wg_noise_keypair_get".
Definition _wg_noise_keypair_put : ident := $"wg_noise_keypair_put".
Definition _wg_noise_keypairs_clear : ident := $"wg_noise_keypairs_clear".
Definition _wg_noise_precompute_static_static : ident := $"wg_noise_precompute_static_static".
Definition _wg_noise_received_with_keypair : ident := $"wg_noise_received_with_keypair".
Definition _wg_noise_reset_last_sent_handshake : ident := $"wg_noise_reset_last_sent_handshake".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_peer_put : ident := $"wg_peer_put".
Definition _wg_pubkey_hashtable_lookup : ident := $"wg_pubkey_hashtable_lookup".
Definition _wg_shim_refcount_dec_and_test : ident := $"wg_shim_refcount_dec_and_test".
Definition _wg_shim_refcount_inc_not_zero : ident := $"wg_shim_refcount_inc_not_zero".
Definition _x_key : ident := $"x_key".
Definition _zero_point : ident := $"zero_point".
Definition _t'1 : ident := 128%positive.
Definition _t'10 : ident := 137%positive.
Definition _t'11 : ident := 138%positive.
Definition _t'12 : ident := 139%positive.
Definition _t'13 : ident := 140%positive.
Definition _t'14 : ident := 141%positive.
Definition _t'15 : ident := 142%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

Definition f_memzero_explicit := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr tvoid)) :: (_count, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                  (tptr tvoid) cc_default))
  ((Etempvar _s (tptr tvoid)) :: (Econst_int (Int.repr 0) tint) ::
   (Etempvar _count tulong) :: nil))
|}.

Definition f_quickproof_rounddown_pow_of_two := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_n, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_r, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _r (Ecast (Econst_int (Int.repr 1) tint) tulong))
  (Ssequence
    (Swhile
      (Ebinop Ole (Etempvar _r tulong)
        (Ebinop Odiv (Etempvar _n tulong) (Econst_int (Int.repr 2) tint)
          tulong) tint)
      (Sset _r
        (Ebinop Omul (Etempvar _r tulong) (Econst_int (Int.repr 2) tint)
          tulong)))
    (Sreturn (Some (Etempvar _r tulong)))))
|}.

Definition f_put_unaligned_be32 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: (_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tuchar)) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _p (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _b (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ecast
        (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 24) tint)
          tuint) tuchar))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Etempvar _b (tptr tuchar))
            (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
        (Ecast
          (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 16) tint)
            tuint) tuchar))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
          (Ecast
            (Ebinop Oshr (Etempvar _v tuint) (Econst_int (Int.repr 8) tint)
              tuint) tuchar))
        (Sassign
          (Ederef
            (Ebinop Oadd (Etempvar _b (tptr tuchar))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
          (Ecast (Etempvar _v tuint) tuchar))))))
|}.

Definition f_put_unaligned_be64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_v, tulong) :: (_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _put_unaligned_be32 (Tfunction (tuint :: (tptr tvoid) :: nil) tvoid
                                cc_default))
    ((Ecast
       (Ebinop Oshr (Etempvar _v tulong) (Econst_int (Int.repr 32) tint)
         tulong) tuint) :: (Etempvar _p (tptr tvoid)) :: nil))
  (Scall None
    (Evar _put_unaligned_be32 (Tfunction (tuint :: (tptr tvoid) :: nil) tvoid
                                cc_default))
    ((Ecast (Etempvar _v tulong) tuint) ::
     (Ebinop Oadd (Ecast (Etempvar _p (tptr tvoid)) (tptr tuchar))
       (Econst_int (Int.repr 4) tint) (tptr tuchar)) :: nil)))
|}.

Definition f_curve25519_clamp_secret := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_secret, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
      (Ebinop Oand (Etempvar _t'2 tuchar) (Econst_int (Int.repr 248) tint)
        tint)))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar))
    (Sassign
      (Ederef
        (Ebinop Oadd (Etempvar _secret (tptr tuchar))
          (Econst_int (Int.repr 31) tint) (tptr tuchar)) tuchar)
      (Ebinop Oor
        (Ebinop Oand (Etempvar _t'1 tuchar) (Econst_int (Int.repr 127) tint)
          tint) (Econst_int (Int.repr 64) tint) tint))))
|}.

Definition f_curve25519_generate_secret := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_secret, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _get_random_bytes_wait (Tfunction ((tptr tvoid) :: tulong :: nil)
                                   tvoid cc_default))
    ((Etempvar _secret (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
     nil))
  (Scall None
    (Evar _curve25519_clamp_secret (Tfunction ((tptr tuchar) :: nil) tvoid
                                     cc_default))
    ((Etempvar _secret (tptr tuchar)) :: nil)))
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

Definition f_wg_noise_reset_last_sent_handshake := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_handshake_ns, (tptr (Tstruct ___gp_atomic64_t noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _ktime_get_coarse_boottime_ns (Tfunction nil tulong cc_default))
    nil)
  (Sassign
    (Efield
      (Ederef
        (Etempvar _handshake_ns (tptr (Tstruct ___gp_atomic64_t noattr)))
        (Tstruct ___gp_atomic64_t noattr)) _counter tlong)
    (Ebinop Osub (Etempvar _t'1 tulong)
      (Ebinop Omul
        (Ecast
          (Ebinop Oadd (Econst_int (Int.repr 5) tint)
            (Econst_int (Int.repr 1) tint) tint) tulong)
        (Econst_long (Int64.repr 1000000000) tlong) tulong) tulong)))
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

Definition v_handshake_name := {|
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

Definition v_identifier_name := {|
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

Definition v_handshake_init_hash := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_handshake_init_chaining_key := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_keypair_counter := {|
  gvar_info := (Tstruct ___gp_atomic64_t noattr);
  gvar_init := (Init_int64 (Int64.repr 0) :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_wg_noise_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_blake, (Tstruct _blake2s_ctx noattr)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _blake2s (Tfunction
                     ((tptr tuchar) :: tulong :: (tptr tuchar) :: tulong ::
                      (tptr tuchar) :: tulong :: nil) tvoid cc_default))
    ((Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
     (Econst_int (Int.repr 0) tint) ::
     (Evar _handshake_name (tarray tuchar 37)) ::
     (Esizeof (tarray tuchar 37) tulong) ::
     (Evar _handshake_init_chaining_key (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _blake2s_init (Tfunction
                            ((tptr (Tstruct _blake2s_ctx noattr)) ::
                             tulong :: nil) tvoid cc_default))
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
         (Evar _handshake_init_chaining_key (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _blake2s_update (Tfunction
                                  ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                   (tptr tuchar) :: tulong :: nil) tvoid
                                  cc_default))
          ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
             (tptr (Tstruct _blake2s_ctx noattr))) ::
           (Evar _identifier_name (tarray tuchar 34)) ::
           (Esizeof (tarray tuchar 34) tulong) :: nil))
        (Scall None
          (Evar _blake2s_final (Tfunction
                                 ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                  (tptr tuchar) :: nil) tvoid cc_default))
          ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
             (tptr (Tstruct _blake2s_ctx noattr))) ::
           (Evar _handshake_init_hash (tarray tuchar 32)) :: nil))))))
|}.

Definition f_wg_noise_precompute_static_static := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tbool) :: (_t'1, tint) ::
               (_t'5, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'4, tbool) ::
               (_t'3, (tptr (Tstruct _noise_static_identity noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Efield
          (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
            (Tstruct _wg_peer noattr)) _handshake
          (Tstruct _noise_handshake noattr)) _static_identity
        (tptr (Tstruct _noise_static_identity noattr))))
    (Ssequence
      (Sset _t'4
        (Efield
          (Ederef
            (Etempvar _t'3 (tptr (Tstruct _noise_static_identity noattr)))
            (Tstruct _noise_static_identity noattr)) _has_identity tbool))
      (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tbool) tint)
        (Sset _t'1 (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Ssequence
            (Sset _t'5
              (Efield
                (Efield
                  (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _handshake
                  (Tstruct _noise_handshake noattr)) _static_identity
                (tptr (Tstruct _noise_static_identity noattr))))
            (Scall (Some _t'2)
              (Evar _curve25519 (Tfunction
                                  ((tptr tuchar) :: (tptr tuchar) ::
                                   (tptr tuchar) :: nil) tbool cc_default))
              ((Efield
                 (Efield
                   (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _handshake
                   (Tstruct _noise_handshake noattr))
                 _precomputed_static_static (tarray tuchar 32)) ::
               (Efield
                 (Ederef
                   (Etempvar _t'5 (tptr (Tstruct _noise_static_identity noattr)))
                   (Tstruct _noise_static_identity noattr)) _static_private
                 (tarray tuchar 32)) ::
               (Efield
                 (Efield
                   (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _handshake
                   (Tstruct _noise_handshake noattr)) _remote_static
                 (tarray tuchar 32)) :: nil)))
          (Sset _t'1
            (Ecast (Eunop Onotbool (Etempvar _t'2 tbool) tint) tbool))))))
  (Sifthenelse (Etempvar _t'1 tint)
    (Scall None
      (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Efield
         (Efield
           (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
             (Tstruct _wg_peer noattr)) _handshake
           (Tstruct _noise_handshake noattr)) _precomputed_static_static
         (tarray tuchar 32)) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    Sskip))
|}.

Definition f_wg_noise_handshake_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                (_static_identity,
                 (tptr (Tstruct _noise_static_identity noattr))) ::
                (_peer_public_key, (tptr tuchar)) ::
                (_peer_preshared_key, (tptr tuchar)) ::
                (_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                    (tptr tvoid) cc_default))
    ((Etempvar _handshake (tptr (Tstruct _noise_handshake noattr))) ::
     (Econst_int (Int.repr 0) tint) ::
     (Esizeof (Tstruct _noise_handshake noattr) tulong) :: nil))
  (Ssequence
    (Sassign
      (Efield
        (Efield
          (Ederef
            (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
            (Tstruct _noise_handshake noattr)) _entry
          (Tstruct _index_hashtable_entry noattr)) _type tint)
      (Econst_int (Int.repr 1) tint))
    (Ssequence
      (Sassign
        (Efield
          (Efield
            (Ederef
              (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
              (Tstruct _noise_handshake noattr)) _entry
            (Tstruct _index_hashtable_entry noattr)) _peer
          (tptr (Tstruct _wg_peer noattr)))
        (Etempvar _peer (tptr (Tstruct _wg_peer noattr))))
      (Ssequence
        (Scall None
          (Evar _memcpy (Tfunction
                          ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                          (tptr tvoid) cc_default))
          ((Efield
             (Ederef
               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
               (Tstruct _noise_handshake noattr)) _remote_static
             (tarray tuchar 32)) ::
           (Etempvar _peer_public_key (tptr tuchar)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Sifthenelse (Etempvar _peer_preshared_key (tptr tuchar))
            (Scall None
              (Evar _memcpy (Tfunction
                              ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                              (tptr tvoid) cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _preshared_key
                 (tarray tuchar 32)) ::
               (Etempvar _peer_preshared_key (tptr tuchar)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            Sskip)
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                  (Tstruct _noise_handshake noattr)) _static_identity
                (tptr (Tstruct _noise_static_identity noattr)))
              (Etempvar _static_identity (tptr (Tstruct _noise_static_identity noattr))))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                    (Tstruct _noise_handshake noattr)) _state tint)
                (Econst_int (Int.repr 0) tint))
              (Scall None
                (Evar _wg_noise_precompute_static_static (Tfunction
                                                           ((tptr (Tstruct _wg_peer noattr)) ::
                                                            nil) tvoid
                                                           cc_default))
                ((Etempvar _peer (tptr (Tstruct _wg_peer noattr))) :: nil)))))))))
|}.

Definition f_handshake_zero := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                    (tptr tvoid) cc_default))
    ((Eaddrof
       (Efield
         (Ederef
           (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
           (Tstruct _noise_handshake noattr)) _ephemeral_private
         (tarray tuchar 32)) (tptr (tarray tuchar 32))) ::
     (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 32) tint) ::
     nil))
  (Ssequence
    (Scall None
      (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Eaddrof
         (Efield
           (Ederef
             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
             (Tstruct _noise_handshake noattr)) _remote_ephemeral
           (tarray tuchar 32)) (tptr (tarray tuchar 32))) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                        (tptr tvoid) cc_default))
        ((Eaddrof
           (Efield
             (Ederef
               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
               (Tstruct _noise_handshake noattr)) _hash (tarray tuchar 32))
           (tptr (tarray tuchar 32))) :: (Econst_int (Int.repr 0) tint) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _memset (Tfunction ((tptr tvoid) :: tint :: tulong :: nil)
                          (tptr tvoid) cc_default))
          ((Eaddrof
             (Efield
               (Ederef
                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                 (Tstruct _noise_handshake noattr)) _chaining_key
               (tarray tuchar 32)) (tptr (tarray tuchar 32))) ::
           (Econst_int (Int.repr 0) tint) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _remote_index tuint)
            (Econst_int (Int.repr 0) tint))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _state tint)
            (Econst_int (Int.repr 0) tint)))))))
|}.

Definition f_wg_noise_handshake_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'3, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'2, (tptr (Tstruct _wg_device noattr))) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'1
      (Efield
        (Efield
          (Ederef
            (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
            (Tstruct _noise_handshake noattr)) _entry
          (Tstruct _index_hashtable_entry noattr)) _peer
        (tptr (Tstruct _wg_peer noattr))))
    (Ssequence
      (Sset _t'2
        (Efield
          (Ederef (Etempvar _t'1 (tptr (Tstruct _wg_peer noattr)))
            (Tstruct _wg_peer noattr)) _device
          (tptr (Tstruct _wg_device noattr))))
      (Ssequence
        (Sset _t'3
          (Efield
            (Ederef (Etempvar _t'2 (tptr (Tstruct _wg_device noattr)))
              (Tstruct _wg_device noattr)) _index_hashtable
            (tptr (Tstruct _index_hashtable noattr))))
        (Scall None
          (Evar _wg_index_hashtable_remove (Tfunction
                                             ((tptr (Tstruct _index_hashtable noattr)) ::
                                              (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                              nil) tvoid cc_default))
          ((Etempvar _t'3 (tptr (Tstruct _index_hashtable noattr))) ::
           (Eaddrof
             (Efield
               (Ederef
                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                 (Tstruct _noise_handshake noattr)) _entry
               (Tstruct _index_hashtable_entry noattr))
             (tptr (Tstruct _index_hashtable_entry noattr))) :: nil)))))
  (Scall None
    (Evar _handshake_zero (Tfunction
                            ((tptr (Tstruct _noise_handshake noattr)) :: nil)
                            tvoid cc_default))
    ((Etempvar _handshake (tptr (Tstruct _noise_handshake noattr))) :: nil)))
|}.

Definition f_keypair_create := {|
  fn_return := (tptr (Tstruct _noise_keypair noattr));
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'2, tlong) :: (_t'1, (tptr tvoid)) :: (_t'3, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _kzalloc (Tfunction (tulong :: tuint :: nil) (tptr tvoid)
                       cc_default))
      ((Esizeof (Tstruct _noise_keypair noattr) tulong) ::
       (Econst_int (Int.repr 0) tuint) :: nil))
    (Sset _keypair (Etempvar _t'1 (tptr tvoid))))
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip)
    (Ssequence
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'3
              (Efield
                (Evar _keypair_counter (Tstruct ___gp_atomic64_t noattr))
                _counter tlong))
            (Sset _t'2
              (Ecast
                (Ecast
                  (Ebinop Oadd (Ecast (Etempvar _t'3 tlong) tulong)
                    (Econst_int (Int.repr 1) tint) tulong) tlong) tlong)))
          (Sassign
            (Efield (Evar _keypair_counter (Tstruct ___gp_atomic64_t noattr))
              _counter tlong) (Etempvar _t'2 tlong)))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
              (Tstruct _noise_keypair noattr)) _internal_id tulong)
          (Etempvar _t'2 tlong)))
      (Ssequence
        (Sassign
          (Efield
            (Efield
              (Ederef
                (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                (Tstruct _noise_keypair noattr)) _entry
              (Tstruct _index_hashtable_entry noattr)) _type tint)
          (Econst_int (Int.repr 2) tint))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef
                  (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                  (Tstruct _noise_keypair noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _peer
              (tptr (Tstruct _wg_peer noattr)))
            (Etempvar _peer (tptr (Tstruct _wg_peer noattr))))
          (Ssequence
            (Sassign
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                    (Tstruct _noise_keypair noattr)) _refcount
                  (Tstruct _kref noattr)) _refcount tuint)
              (Econst_int (Int.repr 1) tint))
            (Sreturn (Some (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))))))))))
|}.

Definition f_keypair_free_rcu := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_rcu, (tptr (Tstruct _rcu_head noattr))) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _kfree_sensitive (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
  ((Ecast
     (Ebinop Osub
       (Ecast (Etempvar _rcu (tptr (Tstruct _rcu_head noattr)))
         (tptr tschar)) (Econst_long (Int64.repr 1188) tulong) (tptr tschar))
     (tptr (Tstruct _noise_keypair noattr))) :: nil))
|}.

Definition f_keypair_free_kref := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_kref__1, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'3, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'2, (tptr (Tstruct _wg_device noattr))) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _keypair
    (Ecast
      (Ebinop Osub
        (Ecast (Etempvar _kref__1 (tptr (Tstruct _kref noattr)))
          (tptr tschar)) (Econst_long (Int64.repr 1184) tulong)
        (tptr tschar)) (tptr (Tstruct _noise_keypair noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'1
        (Efield
          (Efield
            (Ederef
              (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
              (Tstruct _noise_keypair noattr)) _entry
            (Tstruct _index_hashtable_entry noattr)) _peer
          (tptr (Tstruct _wg_peer noattr))))
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef (Etempvar _t'1 (tptr (Tstruct _wg_peer noattr)))
              (Tstruct _wg_peer noattr)) _device
            (tptr (Tstruct _wg_device noattr))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _t'2 (tptr (Tstruct _wg_device noattr)))
                (Tstruct _wg_device noattr)) _index_hashtable
              (tptr (Tstruct _index_hashtable noattr))))
          (Scall None
            (Evar _wg_index_hashtable_remove (Tfunction
                                               ((tptr (Tstruct _index_hashtable noattr)) ::
                                                (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                nil) tvoid cc_default))
            ((Etempvar _t'3 (tptr (Tstruct _index_hashtable noattr))) ::
             (Eaddrof
               (Efield
                 (Ederef
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   (Tstruct _noise_keypair noattr)) _entry
                 (Tstruct _index_hashtable_entry noattr))
               (tptr (Tstruct _index_hashtable_entry noattr))) :: nil)))))
    (Scall None
      (Evar _keypair_free_rcu (Tfunction
                                ((tptr (Tstruct _rcu_head noattr)) :: nil)
                                tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
             (Tstruct _noise_keypair noattr)) _rcu
           (Tstruct _rcu_head noattr)) (tptr (Tstruct _rcu_head noattr))) ::
       nil))))
|}.

Definition f_wg_noise_keypair_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
                (_unreference_now, tbool) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) ::
               (_t'4, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'3, (tptr (Tstruct _wg_device noattr))) ::
               (_t'2, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                 tint)
    (Sreturn None)
    Sskip)
  (Ssequence
    (Sifthenelse (Etempvar _unreference_now tbool)
      (Ssequence
        (Sset _t'2
          (Efield
            (Efield
              (Ederef
                (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                (Tstruct _noise_keypair noattr)) _entry
              (Tstruct _index_hashtable_entry noattr)) _peer
            (tptr (Tstruct _wg_peer noattr))))
        (Ssequence
          (Sset _t'3
            (Efield
              (Ederef (Etempvar _t'2 (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _device
              (tptr (Tstruct _wg_device noattr))))
          (Ssequence
            (Sset _t'4
              (Efield
                (Ederef (Etempvar _t'3 (tptr (Tstruct _wg_device noattr)))
                  (Tstruct _wg_device noattr)) _index_hashtable
                (tptr (Tstruct _index_hashtable noattr))))
            (Scall None
              (Evar _wg_index_hashtable_remove (Tfunction
                                                 ((tptr (Tstruct _index_hashtable noattr)) ::
                                                  (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                  nil) tvoid cc_default))
              ((Etempvar _t'4 (tptr (Tstruct _index_hashtable noattr))) ::
               (Eaddrof
                 (Efield
                   (Ederef
                     (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                     (Tstruct _noise_keypair noattr)) _entry
                   (Tstruct _index_hashtable_entry noattr))
                 (tptr (Tstruct _index_hashtable_entry noattr))) :: nil)))))
      Sskip)
    (Sloop
      (Ssequence
        (Scall (Some _t'1)
          (Evar _wg_shim_refcount_dec_and_test (Tfunction
                                                 ((tptr tuint) :: nil) tbool
                                                 cc_default))
          ((Eaddrof
             (Efield
               (Efield
                 (Ederef
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   (Tstruct _noise_keypair noattr)) _refcount
                 (Tstruct _kref noattr)) _refcount tuint) (tptr tuint)) ::
           nil))
        (Sifthenelse (Etempvar _t'1 tbool)
          (Scall None
            (Evar _keypair_free_kref (Tfunction
                                       ((tptr (Tstruct _kref noattr)) :: nil)
                                       tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   (Tstruct _noise_keypair noattr)) _refcount
                 (Tstruct _kref noattr)) (tptr (Tstruct _kref noattr))) ::
             nil))
          Sskip))
      Sbreak)))
|}.

Definition f_wg_noise_keypair_get := {|
  fn_return := (tptr (Tstruct _noise_keypair noattr));
  fn_callconv := cc_default;
  fn_params := ((_keypair, (tptr (Tstruct _noise_keypair noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tbool) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Scall (Some _t'2)
          (Evar _wg_shim_refcount_inc_not_zero (Tfunction
                                                 ((tptr tuint) :: nil) tbool
                                                 cc_default))
          ((Eaddrof
             (Efield
               (Efield
                 (Ederef
                   (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                   (Tstruct _noise_keypair noattr)) _refcount
                 (Tstruct _kref noattr)) _refcount tuint) (tptr tuint)) ::
           nil))
        (Sset _t'1 (Ecast (Eunop Onotbool (Etempvar _t'2 tbool) tint) tbool))))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip))
  (Sreturn (Some (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr))))))
|}.

Definition f_wg_noise_keypairs_clear := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_keypairs, (tptr (Tstruct _noise_keypairs noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_old, (tptr (Tstruct _noise_keypair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _old
    (Efield
      (Ederef (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
        (Tstruct _noise_keypairs noattr)) _next_keypair
      (tptr (Tstruct _noise_keypair noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
          (Tstruct _noise_keypairs noattr)) _next_keypair
        (tptr (Tstruct _noise_keypair noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Scall None
        (Evar _wg_noise_keypair_put (Tfunction
                                      ((tptr (Tstruct _noise_keypair noattr)) ::
                                       tbool :: nil) tvoid cc_default))
        ((Etempvar _old (tptr (Tstruct _noise_keypair noattr))) ::
         (Econst_int (Int.repr 1) tint) :: nil))
      (Ssequence
        (Sset _old
          (Efield
            (Ederef
              (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
              (Tstruct _noise_keypairs noattr)) _previous_keypair
            (tptr (Tstruct _noise_keypair noattr))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                (Tstruct _noise_keypairs noattr)) _previous_keypair
              (tptr (Tstruct _noise_keypair noattr)))
            (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
          (Ssequence
            (Scall None
              (Evar _wg_noise_keypair_put (Tfunction
                                            ((tptr (Tstruct _noise_keypair noattr)) ::
                                             tbool :: nil) tvoid cc_default))
              ((Etempvar _old (tptr (Tstruct _noise_keypair noattr))) ::
               (Econst_int (Int.repr 1) tint) :: nil))
            (Ssequence
              (Sset _old
                (Efield
                  (Ederef
                    (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                    (Tstruct _noise_keypairs noattr)) _current_keypair
                  (tptr (Tstruct _noise_keypair noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                      (Tstruct _noise_keypairs noattr)) _current_keypair
                    (tptr (Tstruct _noise_keypair noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Scall None
                  (Evar _wg_noise_keypair_put (Tfunction
                                                ((tptr (Tstruct _noise_keypair noattr)) ::
                                                 tbool :: nil) tvoid
                                                cc_default))
                  ((Etempvar _old (tptr (Tstruct _noise_keypair noattr))) ::
                   (Econst_int (Int.repr 1) tint) :: nil))))))))))
|}.

Definition f_wg_noise_expire_current_peer_keypairs := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_keypair, (tptr (Tstruct _noise_keypair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _wg_noise_handshake_clear (Tfunction
                                      ((tptr (Tstruct _noise_handshake noattr)) ::
                                       nil) tvoid cc_default))
    ((Eaddrof
       (Efield
         (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
           (Tstruct _wg_peer noattr)) _handshake
         (Tstruct _noise_handshake noattr))
       (tptr (Tstruct _noise_handshake noattr))) :: nil))
  (Ssequence
    (Scall None
      (Evar _wg_noise_reset_last_sent_handshake (Tfunction
                                                  ((tptr (Tstruct ___gp_atomic64_t noattr)) ::
                                                   nil) tvoid cc_default))
      ((Eaddrof
         (Efield
           (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
             (Tstruct _wg_peer noattr)) _last_sent_handshake
           (Tstruct ___gp_atomic64_t noattr))
         (tptr (Tstruct ___gp_atomic64_t noattr))) :: nil))
    (Ssequence
      (Sset _keypair
        (Efield
          (Efield
            (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
              (Tstruct _wg_peer noattr)) _keypairs
            (Tstruct _noise_keypairs noattr)) _next_keypair
          (tptr (Tstruct _noise_keypair noattr))))
      (Ssequence
        (Sifthenelse (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
          (Sassign
            (Efield
              (Efield
                (Ederef
                  (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                  (Tstruct _noise_keypair noattr)) _sending
                (Tstruct _noise_symmetric_key noattr)) _is_valid tbool)
            (Econst_int (Int.repr 0) tint))
          Sskip)
        (Ssequence
          (Sset _keypair
            (Efield
              (Efield
                (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _keypairs
                (Tstruct _noise_keypairs noattr)) _current_keypair
              (tptr (Tstruct _noise_keypair noattr))))
          (Sifthenelse (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
            (Sassign
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _keypair (tptr (Tstruct _noise_keypair noattr)))
                    (Tstruct _noise_keypair noattr)) _sending
                  (Tstruct _noise_symmetric_key noattr)) _is_valid tbool)
              (Econst_int (Int.repr 0) tint))
            Sskip))))))
|}.

Definition f_add_new_keypair := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_keypairs, (tptr (Tstruct _noise_keypairs noattr))) ::
                (_new_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_previous_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_next_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_current_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _previous_keypair
    (Efield
      (Ederef (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
        (Tstruct _noise_keypairs noattr)) _previous_keypair
      (tptr (Tstruct _noise_keypair noattr))))
  (Ssequence
    (Sset _next_keypair
      (Efield
        (Ederef (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
          (Tstruct _noise_keypairs noattr)) _next_keypair
        (tptr (Tstruct _noise_keypair noattr))))
    (Ssequence
      (Sset _current_keypair
        (Efield
          (Ederef
            (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
            (Tstruct _noise_keypairs noattr)) _current_keypair
          (tptr (Tstruct _noise_keypair noattr))))
      (Ssequence
        (Sset _t'1
          (Efield
            (Ederef
              (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
              (Tstruct _noise_keypair noattr)) _i_am_the_initiator tbool))
        (Sifthenelse (Etempvar _t'1 tbool)
          (Ssequence
            (Sifthenelse (Etempvar _next_keypair (tptr (Tstruct _noise_keypair noattr)))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                      (Tstruct _noise_keypairs noattr)) _next_keypair
                    (tptr (Tstruct _noise_keypair noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Ssequence
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                        (Tstruct _noise_keypairs noattr)) _previous_keypair
                      (tptr (Tstruct _noise_keypair noattr)))
                    (Etempvar _next_keypair (tptr (Tstruct _noise_keypair noattr))))
                  (Scall None
                    (Evar _wg_noise_keypair_put (Tfunction
                                                  ((tptr (Tstruct _noise_keypair noattr)) ::
                                                   tbool :: nil) tvoid
                                                  cc_default))
                    ((Etempvar _current_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                     (Econst_int (Int.repr 1) tint) :: nil))))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                    (Tstruct _noise_keypairs noattr)) _previous_keypair
                  (tptr (Tstruct _noise_keypair noattr)))
                (Etempvar _current_keypair (tptr (Tstruct _noise_keypair noattr)))))
            (Ssequence
              (Scall None
                (Evar _wg_noise_keypair_put (Tfunction
                                              ((tptr (Tstruct _noise_keypair noattr)) ::
                                               tbool :: nil) tvoid
                                              cc_default))
                ((Etempvar _previous_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                 (Econst_int (Int.repr 1) tint) :: nil))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                    (Tstruct _noise_keypairs noattr)) _current_keypair
                  (tptr (Tstruct _noise_keypair noattr)))
                (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr))))))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                  (Tstruct _noise_keypairs noattr)) _next_keypair
                (tptr (Tstruct _noise_keypair noattr)))
              (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr))))
            (Ssequence
              (Scall None
                (Evar _wg_noise_keypair_put (Tfunction
                                              ((tptr (Tstruct _noise_keypair noattr)) ::
                                               tbool :: nil) tvoid
                                              cc_default))
                ((Etempvar _next_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                 (Econst_int (Int.repr 1) tint) :: nil))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                      (Tstruct _noise_keypairs noattr)) _previous_keypair
                    (tptr (Tstruct _noise_keypair noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Scall None
                  (Evar _wg_noise_keypair_put (Tfunction
                                                ((tptr (Tstruct _noise_keypair noattr)) ::
                                                 tbool :: nil) tvoid
                                                cc_default))
                  ((Etempvar _previous_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                   (Econst_int (Int.repr 1) tint) :: nil))))))))))
|}.

Definition f_wg_noise_received_with_keypair := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_keypairs, (tptr (Tstruct _noise_keypairs noattr))) ::
                (_received_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_old_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_key_is_new, tbool) ::
               (_t'3, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'2, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'1, (tptr (Tstruct _noise_keypair noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'3
      (Efield
        (Ederef (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
          (Tstruct _noise_keypairs noattr)) _next_keypair
        (tptr (Tstruct _noise_keypair noattr))))
    (Sset _key_is_new
      (Ecast
        (Ebinop Oeq
          (Etempvar _received_keypair (tptr (Tstruct _noise_keypair noattr)))
          (Etempvar _t'3 (tptr (Tstruct _noise_keypair noattr))) tint) tbool)))
  (Ssequence
    (Sifthenelse (Eunop Onotbool (Etempvar _key_is_new tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Ssequence
        (Sset _t'2
          (Efield
            (Ederef
              (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
              (Tstruct _noise_keypairs noattr)) _next_keypair
            (tptr (Tstruct _noise_keypair noattr))))
        (Sifthenelse (Ebinop One
                       (Etempvar _received_keypair (tptr (Tstruct _noise_keypair noattr)))
                       (Etempvar _t'2 (tptr (Tstruct _noise_keypair noattr)))
                       tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip))
      (Ssequence
        (Sset _old_keypair
          (Efield
            (Ederef
              (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
              (Tstruct _noise_keypairs noattr)) _previous_keypair
            (tptr (Tstruct _noise_keypair noattr))))
        (Ssequence
          (Ssequence
            (Sset _t'1
              (Efield
                (Ederef
                  (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                  (Tstruct _noise_keypairs noattr)) _current_keypair
                (tptr (Tstruct _noise_keypair noattr))))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                  (Tstruct _noise_keypairs noattr)) _previous_keypair
                (tptr (Tstruct _noise_keypair noattr)))
              (Etempvar _t'1 (tptr (Tstruct _noise_keypair noattr)))))
          (Ssequence
            (Scall None
              (Evar _wg_noise_keypair_put (Tfunction
                                            ((tptr (Tstruct _noise_keypair noattr)) ::
                                             tbool :: nil) tvoid cc_default))
              ((Etempvar _old_keypair (tptr (Tstruct _noise_keypair noattr))) ::
               (Econst_int (Int.repr 1) tint) :: nil))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                    (Tstruct _noise_keypairs noattr)) _current_keypair
                  (tptr (Tstruct _noise_keypair noattr)))
                (Etempvar _received_keypair (tptr (Tstruct _noise_keypair noattr))))
              (Ssequence
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr)))
                      (Tstruct _noise_keypairs noattr)) _next_keypair
                    (tptr (Tstruct _noise_keypair noattr)))
                  (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
                (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))))))
|}.

Definition f_wg_noise_set_static_identity_private_key := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_static_identity,
                 (tptr (Tstruct _noise_static_identity noattr))) ::
                (_private_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memcpy (Tfunction ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                    (tptr tvoid) cc_default))
    ((Efield
       (Ederef
         (Etempvar _static_identity (tptr (Tstruct _noise_static_identity noattr)))
         (Tstruct _noise_static_identity noattr)) _static_private
       (tarray tuchar 32)) :: (Etempvar _private_key (tptr tuchar)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _curve25519_clamp_secret (Tfunction ((tptr tuchar) :: nil) tvoid
                                       cc_default))
      ((Efield
         (Ederef
           (Etempvar _static_identity (tptr (Tstruct _noise_static_identity noattr)))
           (Tstruct _noise_static_identity noattr)) _static_private
         (tarray tuchar 32)) :: nil))
    (Ssequence
      (Scall (Some _t'1)
        (Evar _curve25519_generate_public (Tfunction
                                            ((tptr tuchar) ::
                                             (tptr tuchar) :: nil) tbool
                                            cc_default))
        ((Efield
           (Ederef
             (Etempvar _static_identity (tptr (Tstruct _noise_static_identity noattr)))
             (Tstruct _noise_static_identity noattr)) _static_public
           (tarray tuchar 32)) :: (Etempvar _private_key (tptr tuchar)) ::
         nil))
      (Sassign
        (Efield
          (Ederef
            (Etempvar _static_identity (tptr (Tstruct _noise_static_identity noattr)))
            (Tstruct _noise_static_identity noattr)) _has_identity tbool)
        (Etempvar _t'1 tbool)))))
|}.

Definition f_hmac := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_out, (tptr tuchar)) :: (_in, (tptr tuchar)) ::
                (_key, (tptr tuchar)) :: (_inlen, tulong) ::
                (_keylen, tulong) :: nil);
  fn_vars := ((_blake, (Tstruct _blake2s_ctx noattr)) ::
              (_x_key, (tarray tuchar 64)) ::
              (_i_hash, (tarray tuchar 32)) :: nil);
  fn_temps := ((_i, tint) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Ederef
      (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
        (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
    (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
          (Econst_int (Int.repr 1) tint) (tptr tuchar)) tuchar)
      (Econst_int (Int.repr 0) tint))
    (Ssequence
      (Sassign
        (Ederef
          (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
            (Econst_int (Int.repr 2) tint) (tptr tuchar)) tuchar)
        (Econst_int (Int.repr 0) tint))
      (Ssequence
        (Sassign
          (Ederef
            (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
              (Econst_int (Int.repr 3) tint) (tptr tuchar)) tuchar)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Sassign
            (Ederef
              (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                (Econst_int (Int.repr 4) tint) (tptr tuchar)) tuchar)
            (Econst_int (Int.repr 0) tint))
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                  (Econst_int (Int.repr 5) tint) (tptr tuchar)) tuchar)
              (Econst_int (Int.repr 0) tint))
            (Ssequence
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                    (Econst_int (Int.repr 6) tint) (tptr tuchar)) tuchar)
                (Econst_int (Int.repr 0) tint))
              (Ssequence
                (Sassign
                  (Ederef
                    (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                      (Econst_int (Int.repr 7) tint) (tptr tuchar)) tuchar)
                  (Econst_int (Int.repr 0) tint))
                (Ssequence
                  (Sassign
                    (Ederef
                      (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                        (Econst_int (Int.repr 8) tint) (tptr tuchar)) tuchar)
                    (Econst_int (Int.repr 0) tint))
                  (Ssequence
                    (Sassign
                      (Ederef
                        (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                          (Econst_int (Int.repr 9) tint) (tptr tuchar))
                        tuchar) (Econst_int (Int.repr 0) tint))
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                            (Econst_int (Int.repr 10) tint) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 0) tint))
                      (Ssequence
                        (Sassign
                          (Ederef
                            (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                              (Econst_int (Int.repr 11) tint) (tptr tuchar))
                            tuchar) (Econst_int (Int.repr 0) tint))
                        (Ssequence
                          (Sassign
                            (Ederef
                              (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                                (Econst_int (Int.repr 12) tint)
                                (tptr tuchar)) tuchar)
                            (Econst_int (Int.repr 0) tint))
                          (Ssequence
                            (Sassign
                              (Ederef
                                (Ebinop Oadd (Evar _x_key (tarray tuchar 64))
                                  (Econst_int (Int.repr 13) tint)
                                  (tptr tuchar)) tuchar)
                              (Econst_int (Int.repr 0) tint))
                            (Ssequence
                              (Sassign
                                (Ederef
                                  (Ebinop Oadd
                                    (Evar _x_key (tarray tuchar 64))
                                    (Econst_int (Int.repr 14) tint)
                                    (tptr tuchar)) tuchar)
                                (Econst_int (Int.repr 0) tint))
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _x_key (tarray tuchar 64))
                                      (Econst_int (Int.repr 15) tint)
                                      (tptr tuchar)) tuchar)
                                  (Econst_int (Int.repr 0) tint))
                                (Ssequence
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Evar _x_key (tarray tuchar 64))
                                        (Econst_int (Int.repr 16) tint)
                                        (tptr tuchar)) tuchar)
                                    (Econst_int (Int.repr 0) tint))
                                  (Ssequence
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Evar _x_key (tarray tuchar 64))
                                          (Econst_int (Int.repr 17) tint)
                                          (tptr tuchar)) tuchar)
                                      (Econst_int (Int.repr 0) tint))
                                    (Ssequence
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Evar _x_key (tarray tuchar 64))
                                            (Econst_int (Int.repr 18) tint)
                                            (tptr tuchar)) tuchar)
                                        (Econst_int (Int.repr 0) tint))
                                      (Ssequence
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Evar _x_key (tarray tuchar 64))
                                              (Econst_int (Int.repr 19) tint)
                                              (tptr tuchar)) tuchar)
                                          (Econst_int (Int.repr 0) tint))
                                        (Ssequence
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Evar _x_key (tarray tuchar 64))
                                                (Econst_int (Int.repr 20) tint)
                                                (tptr tuchar)) tuchar)
                                            (Econst_int (Int.repr 0) tint))
                                          (Ssequence
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Evar _x_key (tarray tuchar 64))
                                                  (Econst_int (Int.repr 21) tint)
                                                  (tptr tuchar)) tuchar)
                                              (Econst_int (Int.repr 0) tint))
                                            (Ssequence
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Evar _x_key (tarray tuchar 64))
                                                    (Econst_int (Int.repr 22) tint)
                                                    (tptr tuchar)) tuchar)
                                                (Econst_int (Int.repr 0) tint))
                                              (Ssequence
                                                (Sassign
                                                  (Ederef
                                                    (Ebinop Oadd
                                                      (Evar _x_key (tarray tuchar 64))
                                                      (Econst_int (Int.repr 23) tint)
                                                      (tptr tuchar)) tuchar)
                                                  (Econst_int (Int.repr 0) tint))
                                                (Ssequence
                                                  (Sassign
                                                    (Ederef
                                                      (Ebinop Oadd
                                                        (Evar _x_key (tarray tuchar 64))
                                                        (Econst_int (Int.repr 24) tint)
                                                        (tptr tuchar))
                                                      tuchar)
                                                    (Econst_int (Int.repr 0) tint))
                                                  (Ssequence
                                                    (Sassign
                                                      (Ederef
                                                        (Ebinop Oadd
                                                          (Evar _x_key (tarray tuchar 64))
                                                          (Econst_int (Int.repr 25) tint)
                                                          (tptr tuchar))
                                                        tuchar)
                                                      (Econst_int (Int.repr 0) tint))
                                                    (Ssequence
                                                      (Sassign
                                                        (Ederef
                                                          (Ebinop Oadd
                                                            (Evar _x_key (tarray tuchar 64))
                                                            (Econst_int (Int.repr 26) tint)
                                                            (tptr tuchar))
                                                          tuchar)
                                                        (Econst_int (Int.repr 0) tint))
                                                      (Ssequence
                                                        (Sassign
                                                          (Ederef
                                                            (Ebinop Oadd
                                                              (Evar _x_key (tarray tuchar 64))
                                                              (Econst_int (Int.repr 27) tint)
                                                              (tptr tuchar))
                                                            tuchar)
                                                          (Econst_int (Int.repr 0) tint))
                                                        (Ssequence
                                                          (Sassign
                                                            (Ederef
                                                              (Ebinop Oadd
                                                                (Evar _x_key (tarray tuchar 64))
                                                                (Econst_int (Int.repr 28) tint)
                                                                (tptr tuchar))
                                                              tuchar)
                                                            (Econst_int (Int.repr 0) tint))
                                                          (Ssequence
                                                            (Sassign
                                                              (Ederef
                                                                (Ebinop Oadd
                                                                  (Evar _x_key (tarray tuchar 64))
                                                                  (Econst_int (Int.repr 29) tint)
                                                                  (tptr tuchar))
                                                                tuchar)
                                                              (Econst_int (Int.repr 0) tint))
                                                            (Ssequence
                                                              (Sassign
                                                                (Ederef
                                                                  (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 30) tint)
                                                                    (tptr tuchar))
                                                                  tuchar)
                                                                (Econst_int (Int.repr 0) tint))
                                                              (Ssequence
                                                                (Sassign
                                                                  (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 31) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                  (Econst_int (Int.repr 0) tint))
                                                                (Ssequence
                                                                  (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 32) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                  (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 33) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 34) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 35) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 36) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 37) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 38) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 39) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 40) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 41) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 42) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 43) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 44) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 45) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 46) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 47) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 48) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 49) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 50) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 51) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 52) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 53) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 55) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 56) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 57) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 58) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 59) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 60) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 61) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 62) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Econst_int (Int.repr 63) tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Ogt
                                                                    (Etempvar _keylen tulong)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_update 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Etempvar _key (tptr tuchar)) ::
                                                                    (Etempvar _keylen tulong) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _blake2s_final 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _x_key (tarray tuchar 64)) ::
                                                                    nil))))
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Evar _x_key (tarray tuchar 64)) ::
                                                                    (Etempvar _key (tptr tuchar)) ::
                                                                    (Etempvar _keylen tulong) ::
                                                                    nil)))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'2
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Etempvar _i tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Etempvar _i tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'2 tuchar)
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    tint))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_update 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _x_key (tarray tuchar 64)) ::
                                                                    (Econst_int (Int.repr 64) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_update 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Etempvar _in (tptr tuchar)) ::
                                                                    (Etempvar _inlen tulong) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_final 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _i_hash (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Ssequence
                                                                    (Sset _i
                                                                    (Econst_int (Int.repr 0) tint))
                                                                    (Sloop
                                                                    (Ssequence
                                                                    (Sifthenelse 
                                                                    (Ebinop Olt
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 64) tint)
                                                                    tint)
                                                                    Sskip
                                                                    Sbreak)
                                                                    (Ssequence
                                                                    (Sset _t'1
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Etempvar _i tint)
                                                                    (tptr tuchar))
                                                                    tuchar))
                                                                    (Sassign
                                                                    (Ederef
                                                                    (Ebinop Oadd
                                                                    (Evar _x_key (tarray tuchar 64))
                                                                    (Etempvar _i tint)
                                                                    (tptr tuchar))
                                                                    tuchar)
                                                                    (Ebinop Oxor
                                                                    (Etempvar _t'1 tuchar)
                                                                    (Ebinop Oxor
                                                                    (Econst_int (Int.repr 92) tint)
                                                                    (Econst_int (Int.repr 54) tint)
                                                                    tint)
                                                                    tint))))
                                                                    (Sset _i
                                                                    (Ebinop Oadd
                                                                    (Etempvar _i tint)
                                                                    (Econst_int (Int.repr 1) tint)
                                                                    tint))))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_init 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_update 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _x_key (tarray tuchar 64)) ::
                                                                    (Econst_int (Int.repr 64) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_update 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _i_hash (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _blake2s_final 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                                                    (tptr tuchar) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _blake (Tstruct _blake2s_ctx noattr))
                                                                    (tptr (Tstruct _blake2s_ctx noattr))) ::
                                                                    (Evar _i_hash (tarray tuchar 32)) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memcpy 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                                    ((Etempvar _out (tptr tuchar)) ::
                                                                    (Evar _i_hash (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil))
                                                                    (Ssequence
                                                                    (Scall None
                                                                    (Evar _memzero_explicit 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _x_key (tarray tuchar 64)) ::
                                                                    (Econst_int (Int.repr 64) tint) ::
                                                                    nil))
                                                                    (Scall None
                                                                    (Evar _memzero_explicit 
                                                                    (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                                                    ((Evar _i_hash (tarray tuchar 32)) ::
                                                                    (Econst_int (Int.repr 32) tint) ::
                                                                    nil)))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))))
|}.

Definition f_kdf := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_first_dst, (tptr tuchar)) ::
                (_second_dst, (tptr tuchar)) ::
                (_third_dst, (tptr tuchar)) :: (_data, (tptr tuchar)) ::
                (_first_len, tulong) :: (_second_len, tulong) ::
                (_third_len, tulong) :: (_data_len, tulong) ::
                (_chaining_key, (tptr tuchar)) :: nil);
  fn_vars := ((_output, (tarray tuchar 33)) ::
              (_secret, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Scall None
      (Evar _hmac (Tfunction
                    ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                     tulong :: tulong :: nil) tvoid cc_default))
      ((Evar _secret (tarray tuchar 32)) :: (Etempvar _data (tptr tuchar)) ::
       (Etempvar _chaining_key (tptr tuchar)) ::
       (Etempvar _data_len tulong) :: (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Ssequence
        (Sifthenelse (Etempvar _first_dst (tptr tuchar))
          (Sset _t'11 (Ecast (Etempvar _first_len tulong) tbool))
          (Sset _t'11 (Econst_int (Int.repr 0) tint)))
        (Sifthenelse (Etempvar _t'11 tint)
          (Ssequence
            (Sassign
              (Ederef
                (Ebinop Oadd (Evar _output (tarray tuchar 33))
                  (Econst_int (Int.repr 0) tint) (tptr tuchar)) tuchar)
              (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall None
                (Evar _hmac (Tfunction
                              ((tptr tuchar) :: (tptr tuchar) ::
                               (tptr tuchar) :: tulong :: tulong :: nil)
                              tvoid cc_default))
                ((Evar _output (tarray tuchar 33)) ::
                 (Evar _output (tarray tuchar 33)) ::
                 (Evar _secret (tarray tuchar 32)) ::
                 (Econst_int (Int.repr 1) tint) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _memcpy (Tfunction
                                  ((tptr tvoid) :: (tptr tvoid) :: tulong ::
                                   nil) (tptr tvoid) cc_default))
                  ((Etempvar _first_dst (tptr tuchar)) ::
                   (Evar _output (tarray tuchar 33)) ::
                   (Etempvar _first_len tulong) :: nil))
                (Ssequence
                  (Sifthenelse (Etempvar _second_dst (tptr tuchar))
                    (Sset _t'10 (Ecast (Etempvar _second_len tulong) tbool))
                    (Sset _t'10 (Econst_int (Int.repr 0) tint)))
                  (Sifthenelse (Etempvar _t'10 tint)
                    (Ssequence
                      (Sassign
                        (Ederef
                          (Ebinop Oadd (Evar _output (tarray tuchar 33))
                            (Econst_int (Int.repr 32) tint) (tptr tuchar))
                          tuchar) (Econst_int (Int.repr 2) tint))
                      (Ssequence
                        (Scall None
                          (Evar _hmac (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: tulong :: tulong ::
                                         nil) tvoid cc_default))
                          ((Evar _output (tarray tuchar 33)) ::
                           (Evar _output (tarray tuchar 33)) ::
                           (Evar _secret (tarray tuchar 32)) ::
                           (Ebinop Oadd (Econst_int (Int.repr 32) tint)
                             (Econst_int (Int.repr 1) tint) tint) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _memcpy (Tfunction
                                            ((tptr tvoid) :: (tptr tvoid) ::
                                             tulong :: nil) (tptr tvoid)
                                            cc_default))
                            ((Etempvar _second_dst (tptr tuchar)) ::
                             (Evar _output (tarray tuchar 33)) ::
                             (Etempvar _second_len tulong) :: nil))
                          (Ssequence
                            (Sifthenelse (Etempvar _third_dst (tptr tuchar))
                              (Sset _t'9
                                (Ecast (Etempvar _third_len tulong) tbool))
                              (Sset _t'9 (Econst_int (Int.repr 0) tint)))
                            (Sifthenelse (Etempvar _t'9 tint)
                              (Ssequence
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Evar _output (tarray tuchar 33))
                                      (Econst_int (Int.repr 32) tint)
                                      (tptr tuchar)) tuchar)
                                  (Econst_int (Int.repr 3) tint))
                                (Ssequence
                                  (Scall None
                                    (Evar _hmac (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   tulong :: nil) tvoid
                                                  cc_default))
                                    ((Evar _output (tarray tuchar 33)) ::
                                     (Evar _output (tarray tuchar 33)) ::
                                     (Evar _secret (tarray tuchar 32)) ::
                                     (Ebinop Oadd
                                       (Econst_int (Int.repr 32) tint)
                                       (Econst_int (Int.repr 1) tint) tint) ::
                                     (Econst_int (Int.repr 32) tint) :: nil))
                                  (Scall None
                                    (Evar _memcpy (Tfunction
                                                    ((tptr tvoid) ::
                                                     (tptr tvoid) ::
                                                     tulong :: nil)
                                                    (tptr tvoid) cc_default))
                                    ((Etempvar _third_dst (tptr tuchar)) ::
                                     (Evar _output (tarray tuchar 33)) ::
                                     (Etempvar _third_len tulong) :: nil))))
                              Sskip)))))
                    Sskip)))))
          Sskip))
      (Ssequence
        (Scall None
          (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                    tvoid cc_default))
          ((Evar _secret (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Scall None
          (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                    tvoid cc_default))
          ((Evar _output (tarray tuchar 33)) ::
           (Ebinop Oadd (Econst_int (Int.repr 32) tint)
             (Econst_int (Int.repr 1) tint) tint) :: nil))))))
|}.

Definition f_derive_keys := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_first_dst, (tptr (Tstruct _noise_symmetric_key noattr))) ::
                (_second_dst, (tptr (Tstruct _noise_symmetric_key noattr))) ::
                (_chaining_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_birthdate, tulong) :: (_t'3, tbool) :: (_t'2, tulong) ::
               (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _ktime_get_coarse_boottime_ns (Tfunction nil tulong cc_default))
      nil)
    (Sset _birthdate (Etempvar _t'1 tulong)))
  (Ssequence
    (Scall None
      (Evar _kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: tulong :: tulong :: tulong :: tulong ::
                    (tptr tuchar) :: nil) tvoid cc_default))
      ((Efield
         (Ederef
           (Etempvar _first_dst (tptr (Tstruct _noise_symmetric_key noattr)))
           (Tstruct _noise_symmetric_key noattr)) _key (tarray tuchar 32)) ::
       (Efield
         (Ederef
           (Etempvar _second_dst (tptr (Tstruct _noise_symmetric_key noattr)))
           (Tstruct _noise_symmetric_key noattr)) _key (tarray tuchar 32)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 0) tint) ::
       (Etempvar _chaining_key (tptr tuchar)) :: nil))
    (Ssequence
      (Ssequence
        (Ssequence
          (Sset _t'2 (Ecast (Etempvar _birthdate tulong) tulong))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _second_dst (tptr (Tstruct _noise_symmetric_key noattr)))
                (Tstruct _noise_symmetric_key noattr)) _birthdate tulong)
            (Etempvar _t'2 tulong)))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _first_dst (tptr (Tstruct _noise_symmetric_key noattr)))
              (Tstruct _noise_symmetric_key noattr)) _birthdate tulong)
          (Etempvar _t'2 tulong)))
      (Ssequence
        (Ssequence
          (Sset _t'3 (Ecast (Econst_int (Int.repr 1) tint) tbool))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _second_dst (tptr (Tstruct _noise_symmetric_key noattr)))
                (Tstruct _noise_symmetric_key noattr)) _is_valid tbool)
            (Etempvar _t'3 tbool)))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _first_dst (tptr (Tstruct _noise_symmetric_key noattr)))
              (Tstruct _noise_symmetric_key noattr)) _is_valid tbool)
          (Etempvar _t'3 tbool))))))
|}.

Definition f_mix_dh := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_chaining_key, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_private, (tptr tuchar)) :: (_public, (tptr tuchar)) :: nil);
  fn_vars := ((_dh_calculation, (tarray tuchar 32)) :: nil);
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _curve25519 (Tfunction
                          ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                           nil) tbool cc_default))
      ((Evar _dh_calculation (tarray tuchar 32)) ::
       (Etempvar _private (tptr tuchar)) ::
       (Etempvar _public (tptr tuchar)) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: tulong :: tulong :: tulong :: tulong ::
                    (tptr tuchar) :: nil) tvoid cc_default))
      ((Etempvar _chaining_key (tptr tuchar)) ::
       (Etempvar _key (tptr tuchar)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Evar _dh_calculation (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Etempvar _chaining_key (tptr tuchar)) :: nil))
    (Ssequence
      (Scall None
        (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                  tvoid cc_default))
        ((Evar _dh_calculation (tarray tuchar 32)) ::
         (Econst_int (Int.repr 32) tint) :: nil))
      (Sreturn (Some (Econst_int (Int.repr 1) tint))))))
|}.

Definition v_zero_point := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_mix_precomputed_dh := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_chaining_key, (tptr tuchar)) :: (_key, (tptr tuchar)) ::
                (_precomputed, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1)
      (Evar _crypto_memneq (Tfunction
                             ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                             tint cc_default))
      ((Etempvar _precomputed (tptr tuchar)) ::
       (Evar _zero_point (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: tulong :: tulong :: tulong :: tulong ::
                    (tptr tuchar) :: nil) tvoid cc_default))
      ((Etempvar _chaining_key (tptr tuchar)) ::
       (Etempvar _key (tptr tuchar)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Etempvar _precomputed (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Etempvar _chaining_key (tptr tuchar)) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_mix_hash := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_hash, (tptr tuchar)) :: (_src, (tptr tuchar)) ::
                (_src_len, tulong) :: nil);
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
       (Etempvar _hash (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
       nil))
    (Ssequence
      (Scall None
        (Evar _blake2s_update (Tfunction
                                ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                 (tptr tuchar) :: tulong :: nil) tvoid
                                cc_default))
        ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _src (tptr tuchar)) :: (Etempvar _src_len tulong) :: nil))
      (Scall None
        (Evar _blake2s_final (Tfunction
                               ((tptr (Tstruct _blake2s_ctx noattr)) ::
                                (tptr tuchar) :: nil) tvoid cc_default))
        ((Eaddrof (Evar _blake (Tstruct _blake2s_ctx noattr))
           (tptr (Tstruct _blake2s_ctx noattr))) ::
         (Etempvar _hash (tptr tuchar)) :: nil)))))
|}.

Definition f_mix_psk := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chaining_key, (tptr tuchar)) :: (_hash, (tptr tuchar)) ::
                (_key, (tptr tuchar)) :: (_psk, (tptr tuchar)) :: nil);
  fn_vars := ((_temp_hash, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _kdf (Tfunction
                 ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                  (tptr tuchar) :: tulong :: tulong :: tulong :: tulong ::
                  (tptr tuchar) :: nil) tvoid cc_default))
    ((Etempvar _chaining_key (tptr tuchar)) ::
     (Evar _temp_hash (tarray tuchar 32)) :: (Etempvar _key (tptr tuchar)) ::
     (Etempvar _psk (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
     (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 32) tint) ::
     (Econst_int (Int.repr 32) tint) ::
     (Etempvar _chaining_key (tptr tuchar)) :: nil))
  (Ssequence
    (Scall None
      (Evar _mix_hash (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
      ((Etempvar _hash (tptr tuchar)) ::
       (Evar _temp_hash (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Scall None
      (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                tvoid cc_default))
      ((Evar _temp_hash (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))))
|}.

Definition f_handshake_init := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_chaining_key, (tptr tuchar)) :: (_hash, (tptr tuchar)) ::
                (_remote_static, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _memcpy (Tfunction ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                    (tptr tvoid) cc_default))
    ((Etempvar _hash (tptr tuchar)) ::
     (Evar _handshake_init_hash (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _memcpy (Tfunction
                      ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Etempvar _chaining_key (tptr tuchar)) ::
       (Evar _handshake_init_chaining_key (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Scall None
      (Evar _mix_hash (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
      ((Etempvar _hash (tptr tuchar)) ::
       (Etempvar _remote_static (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))))
|}.

Definition f_message_encrypt := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst_ciphertext, (tptr tuchar)) ::
                (_src_plaintext, (tptr tuchar)) :: (_src_len, tulong) ::
                (_key, (tptr tuchar)) :: (_hash, (tptr tuchar)) :: nil);
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
    ((Etempvar _dst_ciphertext (tptr tuchar)) ::
     (Etempvar _src_plaintext (tptr tuchar)) :: (Etempvar _src_len tulong) ::
     (Etempvar _hash (tptr tuchar)) :: (Econst_int (Int.repr 32) tint) ::
     (Econst_int (Int.repr 0) tint) :: (Etempvar _key (tptr tuchar)) :: nil))
  (Scall None
    (Evar _mix_hash (Tfunction
                      ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil) tvoid
                      cc_default))
    ((Etempvar _hash (tptr tuchar)) ::
     (Etempvar _dst_ciphertext (tptr tuchar)) ::
     (Ebinop Oadd (Etempvar _src_len tulong) (Econst_int (Int.repr 16) tint)
       tulong) :: nil)))
|}.

Definition f_message_decrypt := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_dst_plaintext, (tptr tuchar)) ::
                (_src_ciphertext, (tptr tuchar)) :: (_src_len, tulong) ::
                (_key, (tptr tuchar)) :: (_hash, (tptr tuchar)) :: nil);
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
      ((Etempvar _dst_plaintext (tptr tuchar)) ::
       (Etempvar _src_ciphertext (tptr tuchar)) ::
       (Etempvar _src_len tulong) :: (Etempvar _hash (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 0) tint) ::
       (Etempvar _key (tptr tuchar)) :: nil))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Scall None
      (Evar _mix_hash (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
      ((Etempvar _hash (tptr tuchar)) ::
       (Etempvar _src_ciphertext (tptr tuchar)) ::
       (Etempvar _src_len tulong) :: nil))
    (Sreturn (Some (Econst_int (Int.repr 1) tint)))))
|}.

Definition f_message_ephemeral := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ephemeral_dst, (tptr tuchar)) ::
                (_ephemeral_src, (tptr tuchar)) ::
                (_chaining_key, (tptr tuchar)) :: (_hash, (tptr tuchar)) ::
                nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Sifthenelse (Ebinop One (Etempvar _ephemeral_dst (tptr tuchar))
                 (Etempvar _ephemeral_src (tptr tuchar)) tint)
    (Scall None
      (Evar _memcpy (Tfunction
                      ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                      (tptr tvoid) cc_default))
      ((Etempvar _ephemeral_dst (tptr tuchar)) ::
       (Etempvar _ephemeral_src (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    Sskip)
  (Ssequence
    (Scall None
      (Evar _mix_hash (Tfunction
                        ((tptr tuchar) :: (tptr tuchar) :: tulong :: nil)
                        tvoid cc_default))
      ((Etempvar _hash (tptr tuchar)) ::
       (Etempvar _ephemeral_src (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Scall None
      (Evar _kdf (Tfunction
                   ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) ::
                    (tptr tuchar) :: tulong :: tulong :: tulong :: tulong ::
                    (tptr tuchar) :: nil) tvoid cc_default))
      ((Etempvar _chaining_key (tptr tuchar)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
       (Etempvar _ephemeral_src (tptr tuchar)) ::
       (Econst_int (Int.repr 32) tint) :: (Econst_int (Int.repr 0) tint) ::
       (Econst_int (Int.repr 0) tint) :: (Econst_int (Int.repr 32) tint) ::
       (Etempvar _chaining_key (tptr tuchar)) :: nil))))
|}.

Definition f_tai64n_now := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_output, (tptr tuchar)) :: nil);
  fn_vars := ((_now, (Tstruct _timespec64 noattr)) :: nil);
  fn_temps := ((_t'1, tulong) :: (_t'4, tlong) :: (_t'3, tlong) ::
               (_t'2, tlong) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _ktime_get_real_ts64 (Tfunction
                                 ((tptr (Tstruct _timespec64 noattr)) :: nil)
                                 tvoid cc_default))
    ((Eaddrof (Evar _now (Tstruct _timespec64 noattr))
       (tptr (Tstruct _timespec64 noattr))) :: nil))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _quickproof_rounddown_pow_of_two (Tfunction (tulong :: nil)
                                                 tulong cc_default))
        ((Ebinop Odiv (Econst_long (Int64.repr 1000000000) tlong)
           (Econst_int (Int.repr 50) tint) tlong) :: nil))
      (Ssequence
        (Sset _t'4
          (Efield (Evar _now (Tstruct _timespec64 noattr)) _tv_nsec tlong))
        (Sassign
          (Efield (Evar _now (Tstruct _timespec64 noattr)) _tv_nsec tlong)
          (Ebinop Oand (Etempvar _t'4 tlong)
            (Eunop Onotint
              (Ebinop Osub (Etempvar _t'1 tulong)
                (Econst_int (Int.repr 1) tint) tulong) tulong) tulong))))
    (Ssequence
      (Ssequence
        (Sset _t'3
          (Efield (Evar _now (Tstruct _timespec64 noattr)) _tv_sec tlong))
        (Scall None
          (Evar _put_unaligned_be64 (Tfunction
                                      (tulong :: (tptr tvoid) :: nil) tvoid
                                      cc_default))
          ((Ebinop Oadd (Econst_long (Int64.repr 4611686018427387914) tulong)
             (Etempvar _t'3 tlong) tulong) ::
           (Etempvar _output (tptr tuchar)) :: nil)))
      (Ssequence
        (Sset _t'2
          (Efield (Evar _now (Tstruct _timespec64 noattr)) _tv_nsec tlong))
        (Scall None
          (Evar _put_unaligned_be32 (Tfunction (tuint :: (tptr tvoid) :: nil)
                                      tvoid cc_default))
          ((Etempvar _t'2 tlong) ::
           (Ebinop Oadd (Etempvar _output (tptr tuchar))
             (Esizeof tulong tulong) (tptr tuchar)) :: nil))))))
|}.

Definition f_wg_noise_handshake_create_initiation := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _message_handshake_initiation noattr))) ::
                (_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                nil);
  fn_vars := ((_timestamp, (tarray tuchar 12)) ::
              (_key, (tarray tuchar 32)) :: nil);
  fn_temps := ((_ret, tbool) :: (_t'4, tuint) :: (_t'3, tbool) ::
               (_t'2, tbool) :: (_t'1, tbool) :: (_t'10, tbool) ::
               (_t'9, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'8, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'7, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'6, (tptr (Tstruct _wg_device noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _ret (Ecast (Econst_int (Int.repr 0) tint) tbool))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef
                (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _static_identity
              (tptr (Tstruct _noise_static_identity noattr))))
          (Ssequence
            (Sset _t'10
              (Efield
                (Ederef
                  (Etempvar _t'9 (tptr (Tstruct _noise_static_identity noattr)))
                  (Tstruct _noise_static_identity noattr)) _has_identity
                tbool))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'10 tbool) tint)
              Sbreak
              Sskip)))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef
                  (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                  (Tstruct _message_handshake_initiation noattr)) _header
                (Tstruct _message_header noattr)) _type tuint)
            (Ecast (Econst_int (Int.repr 1) tint) tuint))
          (Ssequence
            (Scall None
              (Evar _handshake_init (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       (tptr tuchar) :: nil) tvoid
                                      cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _chaining_key
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef
                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _hash
                 (tarray tuchar 32)) ::
               (Efield
                 (Ederef
                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _remote_static
                 (tarray tuchar 32)) :: nil))
            (Ssequence
              (Scall None
                (Evar _curve25519_generate_secret (Tfunction
                                                    ((tptr tuchar) :: nil)
                                                    tvoid cc_default))
                ((Efield
                   (Ederef
                     (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                     (Tstruct _noise_handshake noattr)) _ephemeral_private
                   (tarray tuchar 32)) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _curve25519_generate_public (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         nil) tbool
                                                        cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                         (Tstruct _message_handshake_initiation noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr))
                       _ephemeral_private (tarray tuchar 32)) :: nil))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
                    Sbreak
                    Sskip))
                (Ssequence
                  (Scall None
                    (Evar _message_ephemeral (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) :: nil) tvoid
                                               cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                         (Tstruct _message_handshake_initiation noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                         (Tstruct _message_handshake_initiation noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr)) _chaining_key
                       (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr)) _hash
                       (tarray tuchar 32)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _mix_dh (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: (tptr tuchar) ::
                                         nil) tbool cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) ::
                         (Evar _key (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _ephemeral_private (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _remote_static (tarray tuchar 32)) :: nil))
                      (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tbool)
                                     tint)
                        Sbreak
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Sset _t'8
                          (Efield
                            (Ederef
                              (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                              (Tstruct _noise_handshake noattr))
                            _static_identity
                            (tptr (Tstruct _noise_static_identity noattr))))
                        (Scall None
                          (Evar _message_encrypt (Tfunction
                                                   ((tptr tuchar) ::
                                                    (tptr tuchar) ::
                                                    tulong ::
                                                    (tptr tuchar) ::
                                                    (tptr tuchar) :: nil)
                                                   tvoid cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                               (Tstruct _message_handshake_initiation noattr))
                             _encrypted_static (tarray tuchar 48)) ::
                           (Efield
                             (Ederef
                               (Etempvar _t'8 (tptr (Tstruct _noise_static_identity noattr)))
                               (Tstruct _noise_static_identity noattr))
                             _static_public (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) ::
                           (Evar _key (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr)) _hash
                             (tarray tuchar 32)) :: nil)))
                      (Ssequence
                        (Ssequence
                          (Scall (Some _t'3)
                            (Evar _mix_precomputed_dh (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         nil) tbool
                                                        cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _chaining_key (tarray tuchar 32)) ::
                             (Evar _key (tarray tuchar 32)) ::
                             (Efield
                               (Ederef
                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _precomputed_static_static (tarray tuchar 32)) ::
                             nil))
                          (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tbool)
                                         tint)
                            Sbreak
                            Sskip))
                        (Ssequence
                          (Scall None
                            (Evar _tai64n_now (Tfunction
                                                ((tptr tuchar) :: nil) tvoid
                                                cc_default))
                            ((Evar _timestamp (tarray tuchar 12)) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _message_encrypt (Tfunction
                                                       ((tptr tuchar) ::
                                                        (tptr tuchar) ::
                                                        tulong ::
                                                        (tptr tuchar) ::
                                                        (tptr tuchar) :: nil)
                                                       tvoid cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                                   (Tstruct _message_handshake_initiation noattr))
                                 _encrypted_timestamp (tarray tuchar 28)) ::
                               (Evar _timestamp (tarray tuchar 12)) ::
                               (Econst_int (Int.repr 12) tint) ::
                               (Evar _key (tarray tuchar 32)) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr)) _hash
                                 (tarray tuchar 32)) :: nil))
                            (Ssequence
                              (Ssequence
                                (Ssequence
                                  (Sset _t'5
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _entry
                                        (Tstruct _index_hashtable_entry noattr))
                                      _peer (tptr (Tstruct _wg_peer noattr))))
                                  (Ssequence
                                    (Sset _t'6
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))
                                          (Tstruct _wg_peer noattr)) _device
                                        (tptr (Tstruct _wg_device noattr))))
                                    (Ssequence
                                      (Sset _t'7
                                        (Efield
                                          (Ederef
                                            (Etempvar _t'6 (tptr (Tstruct _wg_device noattr)))
                                            (Tstruct _wg_device noattr))
                                          _index_hashtable
                                          (tptr (Tstruct _index_hashtable noattr))))
                                      (Scall (Some _t'4)
                                        (Evar _wg_index_hashtable_insert 
                                        (Tfunction
                                          ((tptr (Tstruct _index_hashtable noattr)) ::
                                           (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                           nil) tuint cc_default))
                                        ((Etempvar _t'7 (tptr (Tstruct _index_hashtable noattr))) ::
                                         (Eaddrof
                                           (Efield
                                             (Ederef
                                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                               (Tstruct _noise_handshake noattr))
                                             _entry
                                             (Tstruct _index_hashtable_entry noattr))
                                           (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                         nil)))))
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _dst (tptr (Tstruct _message_handshake_initiation noattr)))
                                      (Tstruct _message_handshake_initiation noattr))
                                    _sender_index tuint)
                                  (Etempvar _t'4 tuint)))
                              (Ssequence
                                (Sassign
                                  (Efield
                                    (Ederef
                                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                      (Tstruct _noise_handshake noattr))
                                    _state tint)
                                  (Econst_int (Int.repr 1) tint))
                                (Sset _ret
                                  (Ecast (Econst_int (Int.repr 1) tint)
                                    tbool)))))))))))))))
      Sbreak)
    (Ssequence
      (Scall None
        (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                  tvoid cc_default))
        ((Evar _key (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Sreturn (Some (Etempvar _ret tbool))))))
|}.

Definition f_wg_noise_handshake_consume_initiation := {|
  fn_return := (tptr (Tstruct _wg_peer noattr));
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr (Tstruct _message_handshake_initiation noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := ((_key, (tarray tuchar 32)) ::
              (_chaining_key, (tarray tuchar 32)) ::
              (_hash, (tarray tuchar 32)) :: (_s, (tarray tuchar 32)) ::
              (_e, (tarray tuchar 32)) :: (_t, (tarray tuchar 12)) :: nil);
  fn_temps := ((_peer, (tptr (Tstruct _wg_peer noattr))) ::
               (_ret_peer, (tptr (Tstruct _wg_peer noattr))) ::
               (_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
               (_replay_attack, tbool) :: (_flood_attack, tbool) ::
               (_initiation_consumption, tulong) :: (_t'10, tulong) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tulong) ::
               (_t'6, tint) :: (_t'5, tbool) :: (_t'4, tbool) ::
               (_t'3, (tptr (Tstruct _wg_peer noattr))) :: (_t'2, tbool) ::
               (_t'1, tbool) :: (_t'15, tbool) ::
               (_t'14, (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (_t'13, tulong) :: (_t'12, tuint) :: (_t'11, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _peer (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Sset _ret_peer (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'15
              (Efield
                (Efield
                  (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                    (Tstruct _wg_device noattr)) _static_identity
                  (Tstruct _noise_static_identity noattr)) _has_identity
                tbool))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'15 tbool) tint)
              Sbreak
              Sskip))
          (Ssequence
            (Scall None
              (Evar _handshake_init (Tfunction
                                      ((tptr tuchar) :: (tptr tuchar) ::
                                       (tptr tuchar) :: nil) tvoid
                                      cc_default))
              ((Evar _chaining_key (tarray tuchar 32)) ::
               (Evar _hash (tarray tuchar 32)) ::
               (Efield
                 (Efield
                   (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                     (Tstruct _wg_device noattr)) _static_identity
                   (Tstruct _noise_static_identity noattr)) _static_public
                 (tarray tuchar 32)) :: nil))
            (Ssequence
              (Scall None
                (Evar _message_ephemeral (Tfunction
                                           ((tptr tuchar) :: (tptr tuchar) ::
                                            (tptr tuchar) :: (tptr tuchar) ::
                                            nil) tvoid cc_default))
                ((Evar _e (tarray tuchar 32)) ::
                 (Efield
                   (Ederef
                     (Etempvar _src (tptr (Tstruct _message_handshake_initiation noattr)))
                     (Tstruct _message_handshake_initiation noattr))
                   _unencrypted_ephemeral (tarray tuchar 32)) ::
                 (Evar _chaining_key (tarray tuchar 32)) ::
                 (Evar _hash (tarray tuchar 32)) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _mix_dh (Tfunction
                                    ((tptr tuchar) :: (tptr tuchar) ::
                                     (tptr tuchar) :: (tptr tuchar) :: nil)
                                    tbool cc_default))
                    ((Evar _chaining_key (tarray tuchar 32)) ::
                     (Evar _key (tarray tuchar 32)) ::
                     (Efield
                       (Efield
                         (Ederef
                           (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                           (Tstruct _wg_device noattr)) _static_identity
                         (Tstruct _noise_static_identity noattr))
                       _static_private (tarray tuchar 32)) ::
                     (Evar _e (tarray tuchar 32)) :: nil))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
                    Sbreak
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'2)
                      (Evar _message_decrypt (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) :: tulong ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) :: nil) tbool
                                               cc_default))
                      ((Evar _s (tarray tuchar 32)) ::
                       (Efield
                         (Ederef
                           (Etempvar _src (tptr (Tstruct _message_handshake_initiation noattr)))
                           (Tstruct _message_handshake_initiation noattr))
                         _encrypted_static (tarray tuchar 48)) ::
                       (Esizeof (tarray tuchar 48) tulong) ::
                       (Evar _key (tarray tuchar 32)) ::
                       (Evar _hash (tarray tuchar 32)) :: nil))
                    (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tbool) tint)
                      Sbreak
                      Sskip))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'14
                          (Efield
                            (Ederef
                              (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                              (Tstruct _wg_device noattr)) _peer_hashtable
                            (tptr (Tstruct _pubkey_hashtable noattr))))
                        (Scall (Some _t'3)
                          (Evar _wg_pubkey_hashtable_lookup (Tfunction
                                                              ((tptr (Tstruct _pubkey_hashtable noattr)) ::
                                                               (tptr tuchar) ::
                                                               nil)
                                                              (tptr (Tstruct _wg_peer noattr))
                                                              cc_default))
                          ((Etempvar _t'14 (tptr (Tstruct _pubkey_hashtable noattr))) ::
                           (Evar _s (tarray tuchar 32)) :: nil)))
                      (Sset _peer
                        (Etempvar _t'3 (tptr (Tstruct _wg_peer noattr)))))
                    (Ssequence
                      (Sifthenelse (Eunop Onotbool
                                     (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                                     tint)
                        Sbreak
                        Sskip)
                      (Ssequence
                        (Sset _handshake
                          (Eaddrof
                            (Efield
                              (Ederef
                                (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                                (Tstruct _wg_peer noattr)) _handshake
                              (Tstruct _noise_handshake noattr))
                            (tptr (Tstruct _noise_handshake noattr))))
                        (Ssequence
                          (Ssequence
                            (Scall (Some _t'4)
                              (Evar _mix_precomputed_dh (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           nil) tbool
                                                          cc_default))
                              ((Evar _chaining_key (tarray tuchar 32)) ::
                               (Evar _key (tarray tuchar 32)) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr))
                                 _precomputed_static_static
                                 (tarray tuchar 32)) :: nil))
                            (Sifthenelse (Eunop Onotbool
                                           (Etempvar _t'4 tbool) tint)
                              Sbreak
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'5)
                                (Evar _message_decrypt (Tfunction
                                                         ((tptr tuchar) ::
                                                          (tptr tuchar) ::
                                                          tulong ::
                                                          (tptr tuchar) ::
                                                          (tptr tuchar) ::
                                                          nil) tbool
                                                         cc_default))
                                ((Evar _t (tarray tuchar 12)) ::
                                 (Efield
                                   (Ederef
                                     (Etempvar _src (tptr (Tstruct _message_handshake_initiation noattr)))
                                     (Tstruct _message_handshake_initiation noattr))
                                   _encrypted_timestamp (tarray tuchar 28)) ::
                                 (Esizeof (tarray tuchar 28) tulong) ::
                                 (Evar _key (tarray tuchar 32)) ::
                                 (Evar _hash (tarray tuchar 32)) :: nil))
                              (Sifthenelse (Eunop Onotbool
                                             (Etempvar _t'5 tbool) tint)
                                Sbreak
                                Sskip))
                            (Ssequence
                              (Ssequence
                                (Scall (Some _t'6)
                                  (Evar _memcmp (Tfunction
                                                  ((tptr tvoid) ::
                                                   (tptr tvoid) :: tulong ::
                                                   nil) tint cc_default))
                                  ((Evar _t (tarray tuchar 12)) ::
                                   (Efield
                                     (Ederef
                                       (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                       (Tstruct _noise_handshake noattr))
                                     _latest_timestamp (tarray tuchar 12)) ::
                                   (Econst_int (Int.repr 12) tint) :: nil))
                                (Sset _replay_attack
                                  (Ecast
                                    (Ebinop Ole (Etempvar _t'6 tint)
                                      (Econst_int (Int.repr 0) tint) tint)
                                    tbool)))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'7)
                                    (Evar _ktime_get_coarse_boottime_ns 
                                    (Tfunction nil tulong cc_default)) nil)
                                  (Ssequence
                                    (Sset _t'13
                                      (Efield
                                        (Ederef
                                          (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _last_initiation_consumption tulong))
                                    (Sset _flood_attack
                                      (Ecast
                                        (Ebinop Ogt
                                          (Ebinop Oadd
                                            (Ecast (Etempvar _t'13 tulong)
                                              tlong)
                                            (Ebinop Odiv
                                              (Econst_long (Int64.repr 1000000000) tlong)
                                              (Econst_int (Int.repr 50) tint)
                                              tlong) tlong)
                                          (Ecast (Etempvar _t'7 tulong)
                                            tlong) tint) tbool))))
                                (Ssequence
                                  (Ssequence
                                    (Sifthenelse (Etempvar _replay_attack tbool)
                                      (Sset _t'8
                                        (Econst_int (Int.repr 1) tint))
                                      (Sset _t'8
                                        (Ecast (Etempvar _flood_attack tbool)
                                          tbool)))
                                    (Sifthenelse (Etempvar _t'8 tint)
                                      Sbreak
                                      Sskip))
                                  (Ssequence
                                    (Scall None
                                      (Evar _memcpy (Tfunction
                                                      ((tptr tvoid) ::
                                                       (tptr tvoid) ::
                                                       tulong :: nil)
                                                      (tptr tvoid)
                                                      cc_default))
                                      ((Efield
                                         (Ederef
                                           (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                           (Tstruct _noise_handshake noattr))
                                         _remote_ephemeral
                                         (tarray tuchar 32)) ::
                                       (Evar _e (tarray tuchar 32)) ::
                                       (Econst_int (Int.repr 32) tint) ::
                                       nil))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'9)
                                          (Evar _memcmp (Tfunction
                                                          ((tptr tvoid) ::
                                                           (tptr tvoid) ::
                                                           tulong :: nil)
                                                          tint cc_default))
                                          ((Evar _t (tarray tuchar 12)) ::
                                           (Efield
                                             (Ederef
                                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                               (Tstruct _noise_handshake noattr))
                                             _latest_timestamp
                                             (tarray tuchar 12)) ::
                                           (Econst_int (Int.repr 12) tint) ::
                                           nil))
                                        (Sifthenelse (Ebinop Ogt
                                                       (Etempvar _t'9 tint)
                                                       (Econst_int (Int.repr 0) tint)
                                                       tint)
                                          (Scall None
                                            (Evar _memcpy (Tfunction
                                                            ((tptr tvoid) ::
                                                             (tptr tvoid) ::
                                                             tulong :: nil)
                                                            (tptr tvoid)
                                                            cc_default))
                                            ((Efield
                                               (Ederef
                                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                 (Tstruct _noise_handshake noattr))
                                               _latest_timestamp
                                               (tarray tuchar 12)) ::
                                             (Evar _t (tarray tuchar 12)) ::
                                             (Econst_int (Int.repr 12) tint) ::
                                             nil))
                                          Sskip))
                                      (Ssequence
                                        (Scall None
                                          (Evar _memcpy (Tfunction
                                                          ((tptr tvoid) ::
                                                           (tptr tvoid) ::
                                                           tulong :: nil)
                                                          (tptr tvoid)
                                                          cc_default))
                                          ((Efield
                                             (Ederef
                                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                               (Tstruct _noise_handshake noattr))
                                             _hash (tarray tuchar 32)) ::
                                           (Evar _hash (tarray tuchar 32)) ::
                                           (Econst_int (Int.repr 32) tint) ::
                                           nil))
                                        (Ssequence
                                          (Scall None
                                            (Evar _memcpy (Tfunction
                                                            ((tptr tvoid) ::
                                                             (tptr tvoid) ::
                                                             tulong :: nil)
                                                            (tptr tvoid)
                                                            cc_default))
                                            ((Efield
                                               (Ederef
                                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                 (Tstruct _noise_handshake noattr))
                                               _chaining_key
                                               (tarray tuchar 32)) ::
                                             (Evar _chaining_key (tarray tuchar 32)) ::
                                             (Econst_int (Int.repr 32) tint) ::
                                             nil))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'12
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _src (tptr (Tstruct _message_handshake_initiation noattr)))
                                                    (Tstruct _message_handshake_initiation noattr))
                                                  _sender_index tuint))
                                              (Sassign
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                    (Tstruct _noise_handshake noattr))
                                                  _remote_index tuint)
                                                (Etempvar _t'12 tuint)))
                                            (Ssequence
                                              (Ssequence
                                                (Scall (Some _t'10)
                                                  (Evar _ktime_get_coarse_boottime_ns 
                                                  (Tfunction nil tulong
                                                    cc_default)) nil)
                                                (Sset _initiation_consumption
                                                  (Etempvar _t'10 tulong)))
                                              (Ssequence
                                                (Ssequence
                                                  (Sset _t'11
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _last_initiation_consumption
                                                      tulong))
                                                  (Sifthenelse (Ebinop Olt
                                                                 (Ecast
                                                                   (Ebinop Osub
                                                                    (Etempvar _t'11 tulong)
                                                                    (Etempvar _initiation_consumption tulong)
                                                                    tulong)
                                                                   tlong)
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 tint)
                                                    (Sassign
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                          (Tstruct _noise_handshake noattr))
                                                        _last_initiation_consumption
                                                        tulong)
                                                      (Etempvar _initiation_consumption tulong))
                                                    Sskip))
                                                (Ssequence
                                                  (Sassign
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _state tint)
                                                    (Econst_int (Int.repr 2) tint))
                                                  (Sset _ret_peer
                                                    (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))))))))))))))))))))))))
        Sbreak)
      (Ssequence
        (Scall None
          (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                    tvoid cc_default))
          ((Evar _key (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _memzero_explicit (Tfunction
                                      ((tptr tvoid) :: tulong :: nil) tvoid
                                      cc_default))
            ((Evar _hash (tarray tuchar 32)) ::
             (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _memzero_explicit (Tfunction
                                        ((tptr tvoid) :: tulong :: nil) tvoid
                                        cc_default))
              ((Evar _chaining_key (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Sifthenelse (Eunop Onotbool
                             (Etempvar _ret_peer (tptr (Tstruct _wg_peer noattr)))
                             tint)
                (Scall None
                  (Evar _wg_peer_put (Tfunction
                                       ((tptr (Tstruct _wg_peer noattr)) ::
                                        nil) tvoid cc_default))
                  ((Etempvar _peer (tptr (Tstruct _wg_peer noattr))) :: nil))
                Sskip)
              (Sreturn (Some (Etempvar _ret_peer (tptr (Tstruct _wg_peer noattr))))))))))))
|}.

Definition f_wg_noise_handshake_create_response := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr (Tstruct _message_handshake_response noattr))) ::
                (_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                nil);
  fn_vars := ((_key, (tarray tuchar 32)) :: nil);
  fn_temps := ((_ret, tbool) :: (_t'4, tuint) :: (_t'3, tbool) ::
               (_t'2, tbool) :: (_t'1, tbool) :: (_t'9, tint) ::
               (_t'8, tuint) ::
               (_t'7, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'6, (tptr (Tstruct _wg_device noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _ret (Ecast (Econst_int (Int.repr 0) tint) tbool))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Sset _t'9
            (Efield
              (Ederef
                (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _state tint))
          (Sifthenelse (Ebinop One (Etempvar _t'9 tint)
                         (Econst_int (Int.repr 2) tint) tint)
            Sbreak
            Sskip))
        (Ssequence
          (Sassign
            (Efield
              (Efield
                (Ederef
                  (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                  (Tstruct _message_handshake_response noattr)) _header
                (Tstruct _message_header noattr)) _type tuint)
            (Ecast (Econst_int (Int.repr 2) tint) tuint))
          (Ssequence
            (Ssequence
              (Sset _t'8
                (Efield
                  (Ederef
                    (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                    (Tstruct _noise_handshake noattr)) _remote_index tuint))
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                    (Tstruct _message_handshake_response noattr))
                  _receiver_index tuint) (Etempvar _t'8 tuint)))
            (Ssequence
              (Scall None
                (Evar _curve25519_generate_secret (Tfunction
                                                    ((tptr tuchar) :: nil)
                                                    tvoid cc_default))
                ((Efield
                   (Ederef
                     (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                     (Tstruct _noise_handshake noattr)) _ephemeral_private
                   (tarray tuchar 32)) :: nil))
              (Ssequence
                (Ssequence
                  (Scall (Some _t'1)
                    (Evar _curve25519_generate_public (Tfunction
                                                        ((tptr tuchar) ::
                                                         (tptr tuchar) ::
                                                         nil) tbool
                                                        cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                         (Tstruct _message_handshake_response noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr))
                       _ephemeral_private (tarray tuchar 32)) :: nil))
                  (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
                    Sbreak
                    Sskip))
                (Ssequence
                  (Scall None
                    (Evar _message_ephemeral (Tfunction
                                               ((tptr tuchar) ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) ::
                                                (tptr tuchar) :: nil) tvoid
                                               cc_default))
                    ((Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                         (Tstruct _message_handshake_response noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                         (Tstruct _message_handshake_response noattr))
                       _unencrypted_ephemeral (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr)) _chaining_key
                       (tarray tuchar 32)) ::
                     (Efield
                       (Ederef
                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                         (Tstruct _noise_handshake noattr)) _hash
                       (tarray tuchar 32)) :: nil))
                  (Ssequence
                    (Ssequence
                      (Scall (Some _t'2)
                        (Evar _mix_dh (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         (tptr tuchar) :: (tptr tuchar) ::
                                         nil) tbool cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) ::
                         (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _ephemeral_private (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr))
                           _remote_ephemeral (tarray tuchar 32)) :: nil))
                      (Sifthenelse (Eunop Onotbool (Etempvar _t'2 tbool)
                                     tint)
                        Sbreak
                        Sskip))
                    (Ssequence
                      (Ssequence
                        (Scall (Some _t'3)
                          (Evar _mix_dh (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           (tptr tuchar) :: (tptr tuchar) ::
                                           nil) tbool cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _chaining_key (tarray tuchar 32)) ::
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _ephemeral_private (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _remote_static (tarray tuchar 32)) :: nil))
                        (Sifthenelse (Eunop Onotbool (Etempvar _t'3 tbool)
                                       tint)
                          Sbreak
                          Sskip))
                      (Ssequence
                        (Scall None
                          (Evar _mix_psk (Tfunction
                                           ((tptr tuchar) :: (tptr tuchar) ::
                                            (tptr tuchar) :: (tptr tuchar) ::
                                            nil) tvoid cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _chaining_key (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr)) _hash
                             (tarray tuchar 32)) ::
                           (Evar _key (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _preshared_key (tarray tuchar 32)) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _message_encrypt (Tfunction
                                                     ((tptr tuchar) ::
                                                      (tptr tuchar) ::
                                                      tulong ::
                                                      (tptr tuchar) ::
                                                      (tptr tuchar) :: nil)
                                                     tvoid cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                                 (Tstruct _message_handshake_response noattr))
                               _encrypted_nothing (tarray tuchar 16)) ::
                             (Ecast (Econst_int (Int.repr 0) tint)
                               (tptr tvoid)) ::
                             (Econst_int (Int.repr 0) tint) ::
                             (Evar _key (tarray tuchar 32)) ::
                             (Efield
                               (Ederef
                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr)) _hash
                               (tarray tuchar 32)) :: nil))
                          (Ssequence
                            (Ssequence
                              (Ssequence
                                (Sset _t'5
                                  (Efield
                                    (Efield
                                      (Ederef
                                        (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                        (Tstruct _noise_handshake noattr))
                                      _entry
                                      (Tstruct _index_hashtable_entry noattr))
                                    _peer (tptr (Tstruct _wg_peer noattr))))
                                (Ssequence
                                  (Sset _t'6
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))
                                        (Tstruct _wg_peer noattr)) _device
                                      (tptr (Tstruct _wg_device noattr))))
                                  (Ssequence
                                    (Sset _t'7
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'6 (tptr (Tstruct _wg_device noattr)))
                                          (Tstruct _wg_device noattr))
                                        _index_hashtable
                                        (tptr (Tstruct _index_hashtable noattr))))
                                    (Scall (Some _t'4)
                                      (Evar _wg_index_hashtable_insert 
                                      (Tfunction
                                        ((tptr (Tstruct _index_hashtable noattr)) ::
                                         (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                         nil) tuint cc_default))
                                      ((Etempvar _t'7 (tptr (Tstruct _index_hashtable noattr))) ::
                                       (Eaddrof
                                         (Efield
                                           (Ederef
                                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                             (Tstruct _noise_handshake noattr))
                                           _entry
                                           (Tstruct _index_hashtable_entry noattr))
                                         (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                       nil)))))
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _dst (tptr (Tstruct _message_handshake_response noattr)))
                                    (Tstruct _message_handshake_response noattr))
                                  _sender_index tuint) (Etempvar _t'4 tuint)))
                            (Ssequence
                              (Sassign
                                (Efield
                                  (Ederef
                                    (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                    (Tstruct _noise_handshake noattr)) _state
                                  tint) (Econst_int (Int.repr 3) tint))
                              (Sset _ret
                                (Ecast (Econst_int (Int.repr 1) tint) tbool))))))))))))))
      Sbreak)
    (Ssequence
      (Scall None
        (Evar _memzero_explicit (Tfunction ((tptr tvoid) :: tulong :: nil)
                                  tvoid cc_default))
        ((Evar _key (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Sreturn (Some (Etempvar _ret tbool))))))
|}.

Definition f_wg_noise_handshake_consume_response := {|
  fn_return := (tptr (Tstruct _wg_peer noattr));
  fn_callconv := cc_default;
  fn_params := ((_src, (tptr (Tstruct _message_handshake_response noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) :: nil);
  fn_vars := ((_peer, (tptr (Tstruct _wg_peer noattr))) ::
              (_key, (tarray tuchar 32)) :: (_hash, (tarray tuchar 32)) ::
              (_chaining_key, (tarray tuchar 32)) ::
              (_e, (tarray tuchar 32)) ::
              (_ephemeral_private, (tarray tuchar 32)) ::
              (_static_private, (tarray tuchar 32)) ::
              (_preshared_key, (tarray tuchar 32)) :: nil);
  fn_temps := ((_state, tint) ::
               (_ret_peer, (tptr (Tstruct _wg_peer noattr))) ::
               (_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
               (_quickproof_success, tbool) :: (_t'4, tbool) ::
               (_t'3, tbool) :: (_t'2, tbool) ::
               (_t'1, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'10, tbool) :: (_t'9, tuint) ::
               (_t'8, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'7, tint) :: (_t'6, tuint) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _state (Econst_int (Int.repr 0) tint))
  (Ssequence
    (Sassign (Evar _peer (tptr (Tstruct _wg_peer noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Sset _ret_peer (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sset _quickproof_success
          (Ecast (Econst_int (Int.repr 0) tint) tbool))
        (Ssequence
          (Sloop
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Efield
                      (Ederef
                        (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                        (Tstruct _wg_device noattr)) _static_identity
                      (Tstruct _noise_static_identity noattr)) _has_identity
                    tbool))
                (Sifthenelse (Eunop Onotbool (Etempvar _t'10 tbool) tint)
                  Sbreak
                  Sskip))
              (Ssequence
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                          (Tstruct _wg_device noattr)) _index_hashtable
                        (tptr (Tstruct _index_hashtable noattr))))
                    (Ssequence
                      (Sset _t'9
                        (Efield
                          (Ederef
                            (Etempvar _src (tptr (Tstruct _message_handshake_response noattr)))
                            (Tstruct _message_handshake_response noattr))
                          _receiver_index tuint))
                      (Scall (Some _t'1)
                        (Evar _wg_index_hashtable_lookup (Tfunction
                                                           ((tptr (Tstruct _index_hashtable noattr)) ::
                                                            tint :: tuint ::
                                                            (tptr (tptr (Tstruct _wg_peer noattr))) ::
                                                            nil)
                                                           (tptr (Tstruct _index_hashtable_entry noattr))
                                                           cc_default))
                        ((Etempvar _t'8 (tptr (Tstruct _index_hashtable noattr))) ::
                         (Econst_int (Int.repr 1) tint) ::
                         (Etempvar _t'9 tuint) ::
                         (Eaddrof
                           (Evar _peer (tptr (Tstruct _wg_peer noattr)))
                           (tptr (tptr (Tstruct _wg_peer noattr)))) :: nil))))
                  (Sset _handshake
                    (Ecast
                      (Etempvar _t'1 (tptr (Tstruct _index_hashtable_entry noattr)))
                      (tptr (Tstruct _noise_handshake noattr)))))
                (Ssequence
                  (Sifthenelse (Eunop Onotbool
                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                 tint)
                    Sbreak
                    Sskip)
                  (Ssequence
                    (Sset _state
                      (Efield
                        (Ederef
                          (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                          (Tstruct _noise_handshake noattr)) _state tint))
                    (Ssequence
                      (Scall None
                        (Evar _memcpy (Tfunction
                                        ((tptr tvoid) :: (tptr tvoid) ::
                                         tulong :: nil) (tptr tvoid)
                                        cc_default))
                        ((Evar _hash (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _hash
                           (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Ssequence
                        (Scall None
                          (Evar _memcpy (Tfunction
                                          ((tptr tvoid) :: (tptr tvoid) ::
                                           tulong :: nil) (tptr tvoid)
                                          cc_default))
                          ((Evar _chaining_key (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _chaining_key (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Ssequence
                          (Scall None
                            (Evar _memcpy (Tfunction
                                            ((tptr tvoid) :: (tptr tvoid) ::
                                             tulong :: nil) (tptr tvoid)
                                            cc_default))
                            ((Evar _ephemeral_private (tarray tuchar 32)) ::
                             (Efield
                               (Ederef
                                 (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _ephemeral_private (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Ssequence
                            (Scall None
                              (Evar _memcpy (Tfunction
                                              ((tptr tvoid) ::
                                               (tptr tvoid) :: tulong :: nil)
                                              (tptr tvoid) cc_default))
                              ((Evar _preshared_key (tarray tuchar 32)) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr))
                                 _preshared_key (tarray tuchar 32)) ::
                               (Econst_int (Int.repr 32) tint) :: nil))
                            (Ssequence
                              (Sloop
                                (Ssequence
                                  (Sifthenelse (Ebinop One
                                                 (Etempvar _state tint)
                                                 (Econst_int (Int.repr 1) tint)
                                                 tint)
                                    Sbreak
                                    Sskip)
                                  (Ssequence
                                    (Scall None
                                      (Evar _message_ephemeral (Tfunction
                                                                 ((tptr tuchar) ::
                                                                  (tptr tuchar) ::
                                                                  (tptr tuchar) ::
                                                                  (tptr tuchar) ::
                                                                  nil) tvoid
                                                                 cc_default))
                                      ((Evar _e (tarray tuchar 32)) ::
                                       (Efield
                                         (Ederef
                                           (Etempvar _src (tptr (Tstruct _message_handshake_response noattr)))
                                           (Tstruct _message_handshake_response noattr))
                                         _unencrypted_ephemeral
                                         (tarray tuchar 32)) ::
                                       (Evar _chaining_key (tarray tuchar 32)) ::
                                       (Evar _hash (tarray tuchar 32)) ::
                                       nil))
                                    (Ssequence
                                      (Ssequence
                                        (Scall (Some _t'2)
                                          (Evar _mix_dh (Tfunction
                                                          ((tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           (tptr tuchar) ::
                                                           nil) tbool
                                                          cc_default))
                                          ((Evar _chaining_key (tarray tuchar 32)) ::
                                           (Ecast
                                             (Econst_int (Int.repr 0) tint)
                                             (tptr tvoid)) ::
                                           (Evar _ephemeral_private (tarray tuchar 32)) ::
                                           (Evar _e (tarray tuchar 32)) ::
                                           nil))
                                        (Sifthenelse (Eunop Onotbool
                                                       (Etempvar _t'2 tbool)
                                                       tint)
                                          Sbreak
                                          Sskip))
                                      (Ssequence
                                        (Ssequence
                                          (Scall (Some _t'3)
                                            (Evar _mix_dh (Tfunction
                                                            ((tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             (tptr tuchar) ::
                                                             nil) tbool
                                                            cc_default))
                                            ((Evar _chaining_key (tarray tuchar 32)) ::
                                             (Ecast
                                               (Econst_int (Int.repr 0) tint)
                                               (tptr tvoid)) ::
                                             (Efield
                                               (Efield
                                                 (Ederef
                                                   (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                                                   (Tstruct _wg_device noattr))
                                                 _static_identity
                                                 (Tstruct _noise_static_identity noattr))
                                               _static_private
                                               (tarray tuchar 32)) ::
                                             (Evar _e (tarray tuchar 32)) ::
                                             nil))
                                          (Sifthenelse (Eunop Onotbool
                                                         (Etempvar _t'3 tbool)
                                                         tint)
                                            Sbreak
                                            Sskip))
                                        (Ssequence
                                          (Scall None
                                            (Evar _mix_psk (Tfunction
                                                             ((tptr tuchar) ::
                                                              (tptr tuchar) ::
                                                              (tptr tuchar) ::
                                                              (tptr tuchar) ::
                                                              nil) tvoid
                                                             cc_default))
                                            ((Evar _chaining_key (tarray tuchar 32)) ::
                                             (Evar _hash (tarray tuchar 32)) ::
                                             (Evar _key (tarray tuchar 32)) ::
                                             (Evar _preshared_key (tarray tuchar 32)) ::
                                             nil))
                                          (Ssequence
                                            (Ssequence
                                              (Scall (Some _t'4)
                                                (Evar _message_decrypt 
                                                (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   (tptr tuchar) ::
                                                   (tptr tuchar) :: nil)
                                                  tbool cc_default))
                                                ((Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) ::
                                                 (Efield
                                                   (Ederef
                                                     (Etempvar _src (tptr (Tstruct _message_handshake_response noattr)))
                                                     (Tstruct _message_handshake_response noattr))
                                                   _encrypted_nothing
                                                   (tarray tuchar 16)) ::
                                                 (Esizeof (tarray tuchar 16) tulong) ::
                                                 (Evar _key (tarray tuchar 32)) ::
                                                 (Evar _hash (tarray tuchar 32)) ::
                                                 nil))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Etempvar _t'4 tbool)
                                                             tint)
                                                Sbreak
                                                Sskip))
                                            (Ssequence
                                              (Ssequence
                                                (Sset _t'7
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _state tint))
                                                (Sifthenelse (Ebinop One
                                                               (Etempvar _t'7 tint)
                                                               (Etempvar _state tint)
                                                               tint)
                                                  Sbreak
                                                  Sskip))
                                              (Ssequence
                                                (Scall None
                                                  (Evar _memcpy (Tfunction
                                                                  ((tptr tvoid) ::
                                                                   (tptr tvoid) ::
                                                                   tulong ::
                                                                   nil)
                                                                  (tptr tvoid)
                                                                  cc_default))
                                                  ((Efield
                                                     (Ederef
                                                       (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                       (Tstruct _noise_handshake noattr))
                                                     _remote_ephemeral
                                                     (tarray tuchar 32)) ::
                                                   (Evar _e (tarray tuchar 32)) ::
                                                   (Econst_int (Int.repr 32) tint) ::
                                                   nil))
                                                (Ssequence
                                                  (Scall None
                                                    (Evar _memcpy (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                    ((Efield
                                                       (Ederef
                                                         (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                         (Tstruct _noise_handshake noattr))
                                                       _hash
                                                       (tarray tuchar 32)) ::
                                                     (Evar _hash (tarray tuchar 32)) ::
                                                     (Econst_int (Int.repr 32) tint) ::
                                                     nil))
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _memcpy (Tfunction
                                                                    ((tptr tvoid) ::
                                                                    (tptr tvoid) ::
                                                                    tulong ::
                                                                    nil)
                                                                    (tptr tvoid)
                                                                    cc_default))
                                                      ((Efield
                                                         (Ederef
                                                           (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                           (Tstruct _noise_handshake noattr))
                                                         _chaining_key
                                                         (tarray tuchar 32)) ::
                                                       (Evar _chaining_key (tarray tuchar 32)) ::
                                                       (Econst_int (Int.repr 32) tint) ::
                                                       nil))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'6
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _src (tptr (Tstruct _message_handshake_response noattr)))
                                                              (Tstruct _message_handshake_response noattr))
                                                            _sender_index
                                                            tuint))
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                              (Tstruct _noise_handshake noattr))
                                                            _remote_index
                                                            tuint)
                                                          (Etempvar _t'6 tuint)))
                                                      (Ssequence
                                                        (Sassign
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                                              (Tstruct _noise_handshake noattr))
                                                            _state tint)
                                                          (Econst_int (Int.repr 4) tint))
                                                        (Ssequence
                                                          (Sset _ret_peer
                                                            (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                                                          (Sset _quickproof_success
                                                            (Ecast
                                                              (Econst_int (Int.repr 1) tint)
                                                              tbool)))))))))))))))
                                Sbreak)
                              (Sifthenelse (Eunop Onotbool
                                             (Etempvar _quickproof_success tbool)
                                             tint)
                                (Ssequence
                                  (Sset _t'5
                                    (Evar _peer (tptr (Tstruct _wg_peer noattr))))
                                  (Scall None
                                    (Evar _wg_peer_put (Tfunction
                                                         ((tptr (Tstruct _wg_peer noattr)) ::
                                                          nil) tvoid
                                                         cc_default))
                                    ((Etempvar _t'5 (tptr (Tstruct _wg_peer noattr))) ::
                                     nil)))
                                Sskip))))))))))
            Sbreak)
          (Ssequence
            (Scall None
              (Evar _memzero_explicit (Tfunction
                                        ((tptr tvoid) :: tulong :: nil) tvoid
                                        cc_default))
              ((Evar _key (tarray tuchar 32)) ::
               (Econst_int (Int.repr 32) tint) :: nil))
            (Ssequence
              (Scall None
                (Evar _memzero_explicit (Tfunction
                                          ((tptr tvoid) :: tulong :: nil)
                                          tvoid cc_default))
                ((Evar _hash (tarray tuchar 32)) ::
                 (Econst_int (Int.repr 32) tint) :: nil))
              (Ssequence
                (Scall None
                  (Evar _memzero_explicit (Tfunction
                                            ((tptr tvoid) :: tulong :: nil)
                                            tvoid cc_default))
                  ((Evar _chaining_key (tarray tuchar 32)) ::
                   (Econst_int (Int.repr 32) tint) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _memzero_explicit (Tfunction
                                              ((tptr tvoid) :: tulong :: nil)
                                              tvoid cc_default))
                    ((Evar _ephemeral_private (tarray tuchar 32)) ::
                     (Econst_int (Int.repr 32) tint) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _memzero_explicit (Tfunction
                                                ((tptr tvoid) :: tulong ::
                                                 nil) tvoid cc_default))
                      ((Evar _static_private (tarray tuchar 32)) ::
                       (Econst_int (Int.repr 32) tint) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _memzero_explicit (Tfunction
                                                  ((tptr tvoid) :: tulong ::
                                                   nil) tvoid cc_default))
                        ((Evar _preshared_key (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Sreturn (Some (Etempvar _ret_peer (tptr (Tstruct _wg_peer noattr))))))))))))))))
|}.

Definition f_wg_noise_handshake_begin_session := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_handshake, (tptr (Tstruct _noise_handshake noattr))) ::
                (_keypairs, (tptr (Tstruct _noise_keypairs noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_new_keypair, (tptr (Tstruct _noise_keypair noattr))) ::
               (_ret, tbool) :: (_t'3, tbool) ::
               (_t'2, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'1, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, (tptr (Tstruct _wg_peer noattr))) :: (_t'10, tint) ::
               (_t'9, tuint) :: (_t'8, tbool) ::
               (_t'7, (tptr (Tstruct _index_hashtable noattr))) ::
               (_t'6, (tptr (Tstruct _wg_device noattr))) ::
               (_t'5, (tptr (Tstruct _wg_peer noattr))) :: (_t'4, tbool) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _ret (Ecast (Econst_int (Int.repr 0) tint) tbool))
  (Ssequence
    (Sloop
      (Ssequence
        (Ssequence
          (Ssequence
            (Sset _t'12
              (Efield
                (Ederef
                  (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                  (Tstruct _noise_handshake noattr)) _state tint))
            (Sifthenelse (Ebinop One (Etempvar _t'12 tint)
                           (Econst_int (Int.repr 3) tint) tint)
              (Ssequence
                (Sset _t'13
                  (Efield
                    (Ederef
                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _state tint))
                (Sset _t'1
                  (Ecast
                    (Ebinop One (Etempvar _t'13 tint)
                      (Econst_int (Int.repr 4) tint) tint) tbool)))
              (Sset _t'1 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'1 tint) Sbreak Sskip))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'11
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _entry
                    (Tstruct _index_hashtable_entry noattr)) _peer
                  (tptr (Tstruct _wg_peer noattr))))
              (Scall (Some _t'2)
                (Evar _keypair_create (Tfunction
                                        ((tptr (Tstruct _wg_peer noattr)) ::
                                         nil)
                                        (tptr (Tstruct _noise_keypair noattr))
                                        cc_default))
                ((Etempvar _t'11 (tptr (Tstruct _wg_peer noattr))) :: nil)))
            (Sset _new_keypair
              (Etempvar _t'2 (tptr (Tstruct _noise_keypair noattr)))))
          (Ssequence
            (Sifthenelse (Eunop Onotbool
                           (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                           tint)
              Sbreak
              Sskip)
            (Ssequence
              (Ssequence
                (Sset _t'10
                  (Efield
                    (Ederef
                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _state tint))
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                      (Tstruct _noise_keypair noattr)) _i_am_the_initiator
                    tbool)
                  (Ebinop Oeq (Etempvar _t'10 tint)
                    (Econst_int (Int.repr 4) tint) tint)))
              (Ssequence
                (Ssequence
                  (Sset _t'9
                    (Efield
                      (Ederef
                        (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                        (Tstruct _noise_handshake noattr)) _remote_index
                      tuint))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                        (Tstruct _noise_keypair noattr)) _remote_index tuint)
                    (Etempvar _t'9 tuint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'8
                      (Efield
                        (Ederef
                          (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                          (Tstruct _noise_keypair noattr))
                        _i_am_the_initiator tbool))
                    (Sifthenelse (Etempvar _t'8 tbool)
                      (Scall None
                        (Evar _derive_keys (Tfunction
                                             ((tptr (Tstruct _noise_symmetric_key noattr)) ::
                                              (tptr (Tstruct _noise_symmetric_key noattr)) ::
                                              (tptr tuchar) :: nil) tvoid
                                             cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                               (Tstruct _noise_keypair noattr)) _sending
                             (Tstruct _noise_symmetric_key noattr))
                           (tptr (Tstruct _noise_symmetric_key noattr))) ::
                         (Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                               (Tstruct _noise_keypair noattr)) _receiving
                             (Tstruct _noise_symmetric_key noattr))
                           (tptr (Tstruct _noise_symmetric_key noattr))) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) :: nil))
                      (Scall None
                        (Evar _derive_keys (Tfunction
                                             ((tptr (Tstruct _noise_symmetric_key noattr)) ::
                                              (tptr (Tstruct _noise_symmetric_key noattr)) ::
                                              (tptr tuchar) :: nil) tvoid
                                             cc_default))
                        ((Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                               (Tstruct _noise_keypair noattr)) _receiving
                             (Tstruct _noise_symmetric_key noattr))
                           (tptr (Tstruct _noise_symmetric_key noattr))) ::
                         (Eaddrof
                           (Efield
                             (Ederef
                               (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                               (Tstruct _noise_keypair noattr)) _sending
                             (Tstruct _noise_symmetric_key noattr))
                           (tptr (Tstruct _noise_symmetric_key noattr))) ::
                         (Efield
                           (Ederef
                             (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) :: nil))))
                  (Ssequence
                    (Scall None
                      (Evar _handshake_zero (Tfunction
                                              ((tptr (Tstruct _noise_handshake noattr)) ::
                                               nil) tvoid cc_default))
                      ((Etempvar _handshake (tptr (Tstruct _noise_handshake noattr))) ::
                       nil))
                    (Ssequence
                      (Sset _t'4
                        (Efield
                          (Ederef
                            (Ecast
                              (Ebinop Osub
                                (Ecast
                                  (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                  (tptr tschar))
                                (Econst_long (Int64.repr 48) tulong)
                                (tptr tschar))
                              (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _is_dead tbool))
                      (Sifthenelse (Eunop Onotbool (Etempvar _t'4 tbool)
                                     tint)
                        (Ssequence
                          (Scall None
                            (Evar _add_new_keypair (Tfunction
                                                     ((tptr (Tstruct _noise_keypairs noattr)) ::
                                                      (tptr (Tstruct _noise_keypair noattr)) ::
                                                      nil) tvoid cc_default))
                            ((Etempvar _keypairs (tptr (Tstruct _noise_keypairs noattr))) ::
                             (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                             nil))
                          (Ssequence
                            (Ssequence
                              (Sset _t'5
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                      (Tstruct _noise_handshake noattr))
                                    _entry
                                    (Tstruct _index_hashtable_entry noattr))
                                  _peer (tptr (Tstruct _wg_peer noattr))))
                              (Ssequence
                                (Sset _t'6
                                  (Efield
                                    (Ederef
                                      (Etempvar _t'5 (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _device
                                    (tptr (Tstruct _wg_device noattr))))
                                (Ssequence
                                  (Sset _t'7
                                    (Efield
                                      (Ederef
                                        (Etempvar _t'6 (tptr (Tstruct _wg_device noattr)))
                                        (Tstruct _wg_device noattr))
                                      _index_hashtable
                                      (tptr (Tstruct _index_hashtable noattr))))
                                  (Scall (Some _t'3)
                                    (Evar _wg_index_hashtable_replace 
                                    (Tfunction
                                      ((tptr (Tstruct _index_hashtable noattr)) ::
                                       (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                       (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                       nil) tbool cc_default))
                                    ((Etempvar _t'7 (tptr (Tstruct _index_hashtable noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Ederef
                                           (Etempvar _handshake (tptr (Tstruct _noise_handshake noattr)))
                                           (Tstruct _noise_handshake noattr))
                                         _entry
                                         (Tstruct _index_hashtable_entry noattr))
                                       (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Ederef
                                           (Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr)))
                                           (Tstruct _noise_keypair noattr))
                                         _entry
                                         (Tstruct _index_hashtable_entry noattr))
                                       (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                     nil)))))
                            (Sset _ret (Ecast (Etempvar _t'3 tbool) tbool))))
                        (Scall None
                          (Evar _kfree_sensitive (Tfunction
                                                   ((tptr tvoid) :: nil)
                                                   tvoid cc_default))
                          ((Etempvar _new_keypair (tptr (Tstruct _noise_keypair noattr))) ::
                           nil)))))))))))
      Sbreak)
    (Sreturn (Some (Etempvar _ret tbool)))))
|}.

Definition composites : list composite_definition :=
(Composite ___gp_spinlock_t Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _rw_semaphore Struct (Member_plain _unused tint :: nil) noattr ::
 Composite _rcu_head Struct (Member_plain _unused tint :: nil) noattr ::
 Composite ___gp_atomic64_t Struct
   (Member_plain _counter tlong :: nil)
   noattr ::
 Composite _kref Struct (Member_plain _refcount tuint :: nil) noattr ::
 Composite _timespec64 Struct
   (Member_plain _tv_sec tlong :: Member_plain _tv_nsec tlong :: nil)
   noattr ::
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
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) tint cc_default)) ::
 (_memzero_explicit, Gfun(Internal f_memzero_explicit)) ::
 (_quickproof_rounddown_pow_of_two, Gfun(Internal f_quickproof_rounddown_pow_of_two)) ::
 (_put_unaligned_be32, Gfun(Internal f_put_unaligned_be32)) ::
 (_put_unaligned_be64, Gfun(Internal f_put_unaligned_be64)) ::
 (_kzalloc,
   Gfun(External (EF_external "kzalloc"
                   (mksignature (AST.Xlong :: AST.Xint :: nil) AST.Xptr
                     cc_default)) (tulong :: tuint :: nil) (tptr tvoid)
     cc_default)) ::
 (_kfree_sensitive,
   Gfun(External (EF_external "kfree_sensitive"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_ktime_get_coarse_boottime_ns,
   Gfun(External (EF_external "ktime_get_coarse_boottime_ns"
                   (mksignature nil AST.Xlong cc_default)) nil tulong
     cc_default)) ::
 (_ktime_get_real_ts64,
   Gfun(External (EF_external "ktime_get_real_ts64"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _timespec64 noattr)) :: nil) tvoid cc_default)) ::
 (_get_random_bytes_wait,
   Gfun(External (EF_external "get_random_bytes_wait"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tvoid) :: tulong :: nil) tvoid
     cc_default)) ::
 (_curve25519,
   Gfun(External (EF_external "curve25519"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xbool cc_default))
     ((tptr tuchar) :: (tptr tuchar) :: (tptr tuchar) :: nil) tbool
     cc_default)) ::
 (_curve25519_generate_public,
   Gfun(External (EF_external "curve25519_generate_public"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xbool
                     cc_default)) ((tptr tuchar) :: (tptr tuchar) :: nil)
     tbool cc_default)) ::
 (_curve25519_clamp_secret, Gfun(Internal f_curve25519_clamp_secret)) ::
 (_curve25519_generate_secret, Gfun(Internal f_curve25519_generate_secret)) ::
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
 (_wg_pubkey_hashtable_lookup,
   Gfun(External (EF_external "wg_pubkey_hashtable_lookup"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xptr
                     cc_default))
     ((tptr (Tstruct _pubkey_hashtable noattr)) :: (tptr tuchar) :: nil)
     (tptr (Tstruct _wg_peer noattr)) cc_default)) ::
 (_wg_index_hashtable_insert,
   Gfun(External (EF_external "wg_index_hashtable_insert"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) :: nil) tuint
     cc_default)) ::
 (_wg_index_hashtable_replace,
   Gfun(External (EF_external "wg_index_hashtable_replace"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xptr :: nil)
                     AST.Xbool cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) :: nil) tbool
     cc_default)) ::
 (_wg_index_hashtable_remove,
   Gfun(External (EF_external "wg_index_hashtable_remove"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xvoid
                     cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) :: nil) tvoid
     cc_default)) ::
 (_wg_index_hashtable_lookup,
   Gfun(External (EF_external "wg_index_hashtable_lookup"
                   (mksignature
                     (AST.Xptr :: AST.Xint :: AST.Xint :: AST.Xptr :: nil)
                     AST.Xptr cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) :: tint :: tuint ::
      (tptr (tptr (Tstruct _wg_peer noattr))) :: nil)
     (tptr (Tstruct _index_hashtable_entry noattr)) cc_default)) ::
 (_wg_shim_refcount_inc_not_zero,
   Gfun(External (EF_external "wg_shim_refcount_inc_not_zero"
                   (mksignature (AST.Xptr :: nil) AST.Xbool cc_default))
     ((tptr tuint) :: nil) tbool cc_default)) ::
 (_wg_shim_refcount_dec_and_test,
   Gfun(External (EF_external "wg_shim_refcount_dec_and_test"
                   (mksignature (AST.Xptr :: nil) AST.Xbool cc_default))
     ((tptr tuint) :: nil) tbool cc_default)) ::
 (_wg_noise_reset_last_sent_handshake, Gfun(Internal f_wg_noise_reset_last_sent_handshake)) ::
 (_wg_peer_put,
   Gfun(External (EF_external "wg_peer_put"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _wg_peer noattr)) :: nil) tvoid cc_default)) ::
 (___crypto_memneq,
   Gfun(External (EF_external "__crypto_memneq"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xlong cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) tulong cc_default)) ::
 (_crypto_memneq, Gfun(Internal f_crypto_memneq)) ::
 (_handshake_name, Gvar v_handshake_name) ::
 (_identifier_name, Gvar v_identifier_name) ::
 (_handshake_init_hash, Gvar v_handshake_init_hash) ::
 (_handshake_init_chaining_key, Gvar v_handshake_init_chaining_key) ::
 (_keypair_counter, Gvar v_keypair_counter) ::
 (_wg_noise_init, Gfun(Internal f_wg_noise_init)) ::
 (_wg_noise_precompute_static_static, Gfun(Internal f_wg_noise_precompute_static_static)) ::
 (_wg_noise_handshake_init, Gfun(Internal f_wg_noise_handshake_init)) ::
 (_handshake_zero, Gfun(Internal f_handshake_zero)) ::
 (_wg_noise_handshake_clear, Gfun(Internal f_wg_noise_handshake_clear)) ::
 (_keypair_create, Gfun(Internal f_keypair_create)) ::
 (_keypair_free_rcu, Gfun(Internal f_keypair_free_rcu)) ::
 (_keypair_free_kref, Gfun(Internal f_keypair_free_kref)) ::
 (_wg_noise_keypair_put, Gfun(Internal f_wg_noise_keypair_put)) ::
 (_wg_noise_keypair_get, Gfun(Internal f_wg_noise_keypair_get)) ::
 (_wg_noise_keypairs_clear, Gfun(Internal f_wg_noise_keypairs_clear)) ::
 (_wg_noise_expire_current_peer_keypairs, Gfun(Internal f_wg_noise_expire_current_peer_keypairs)) ::
 (_add_new_keypair, Gfun(Internal f_add_new_keypair)) ::
 (_wg_noise_received_with_keypair, Gfun(Internal f_wg_noise_received_with_keypair)) ::
 (_wg_noise_set_static_identity_private_key, Gfun(Internal f_wg_noise_set_static_identity_private_key)) ::
 (_hmac, Gfun(Internal f_hmac)) :: (_kdf, Gfun(Internal f_kdf)) ::
 (_derive_keys, Gfun(Internal f_derive_keys)) ::
 (_mix_dh, Gfun(Internal f_mix_dh)) :: (_zero_point, Gvar v_zero_point) ::
 (_mix_precomputed_dh, Gfun(Internal f_mix_precomputed_dh)) ::
 (_mix_hash, Gfun(Internal f_mix_hash)) ::
 (_mix_psk, Gfun(Internal f_mix_psk)) ::
 (_handshake_init, Gfun(Internal f_handshake_init)) ::
 (_message_encrypt, Gfun(Internal f_message_encrypt)) ::
 (_message_decrypt, Gfun(Internal f_message_decrypt)) ::
 (_message_ephemeral, Gfun(Internal f_message_ephemeral)) ::
 (_tai64n_now, Gfun(Internal f_tai64n_now)) ::
 (_wg_noise_handshake_create_initiation, Gfun(Internal f_wg_noise_handshake_create_initiation)) ::
 (_wg_noise_handshake_consume_initiation, Gfun(Internal f_wg_noise_handshake_consume_initiation)) ::
 (_wg_noise_handshake_create_response, Gfun(Internal f_wg_noise_handshake_create_response)) ::
 (_wg_noise_handshake_consume_response, Gfun(Internal f_wg_noise_handshake_consume_response)) ::
 (_wg_noise_handshake_begin_session, Gfun(Internal f_wg_noise_handshake_begin_session)) ::
 nil).

Definition public_idents : list ident :=
(_wg_noise_handshake_begin_session :: _wg_noise_handshake_consume_response ::
 _wg_noise_handshake_create_response ::
 _wg_noise_handshake_consume_initiation ::
 _wg_noise_handshake_create_initiation ::
 _wg_noise_set_static_identity_private_key ::
 _wg_noise_received_with_keypair :: _wg_noise_expire_current_peer_keypairs ::
 _wg_noise_keypairs_clear :: _wg_noise_keypair_get ::
 _wg_noise_keypair_put :: _wg_noise_handshake_clear ::
 _wg_noise_handshake_init :: _wg_noise_precompute_static_static ::
 _wg_noise_init :: ___crypto_memneq :: _wg_peer_put ::
 _wg_shim_refcount_dec_and_test :: _wg_shim_refcount_inc_not_zero ::
 _wg_index_hashtable_lookup :: _wg_index_hashtable_remove ::
 _wg_index_hashtable_replace :: _wg_index_hashtable_insert ::
 _wg_pubkey_hashtable_lookup :: _blake2s_final :: _blake2s_update ::
 _chacha20poly1305_decrypt :: _chacha20poly1305_encrypt ::
 _curve25519_generate_public :: _curve25519 :: _get_random_bytes_wait ::
 _ktime_get_real_ts64 :: _ktime_get_coarse_boottime_ns :: _kfree_sensitive ::
 _kzalloc :: _memcmp :: _memset :: _memcpy :: ___builtin_debug ::
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


