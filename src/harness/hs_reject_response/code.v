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
  Definition source_file := "harness/hs_reject_response.c".
  Definition normalized := true.
End Info.

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
Definition _a_indices : ident := $"a_indices".
Definition _a_keys : ident := $"a_keys".
Definition _a_peer : ident := $"a_peer".
Definition _a_private : ident := $"a_private".
Definition _any_clocks : ident := $"any_clocks".
Definition _any_u64 : ident := $"any_u64".
Definition _b : ident := $"b".
Definition _b_indices : ident := $"b_indices".
Definition _b_keys : ident := $"b_keys".
Definition _b_peer : ident := $"b_peer".
Definition _b_private : ident := $"b_private".
Definition _backtrack : ident := $"backtrack".
Definition _before : ident := $"before".
Definition _birthdate : ident := $"birthdate".
Definition _bytes_eq : ident := $"bytes_eq".
Definition _chaining_key : ident := $"chaining_key".
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _copy_peer : ident := $"copy_peer".
Definition _counter : ident := $"counter".
Definition _current_keypair : ident := $"current_keypair".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _encrypted_nothing : ident := $"encrypted_nothing".
Definition _encrypted_static : ident := $"encrypted_static".
Definition _encrypted_timestamp : ident := $"encrypted_timestamp".
Definition _entry : ident := $"entry".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _found : ident := $"found".
Definition _from : ident := $"from".
Definition _gp_assert : ident := $"gp_assert".
Definition _h : ident := $"h".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _header : ident := $"header".
Definition _high : ident := $"high".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _indices : ident := $"indices".
Definition _initiated : ident := $"initiated".
Definition _initiation : ident := $"initiation".
Definition _internal_id : ident := $"internal_id".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _key : ident := $"key".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _keys : ident := $"keys".
Definition _kref : ident := $"kref".
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
Definition _message : ident := $"message".
Definition _message_handshake_initiation : ident := $"message_handshake_initiation".
Definition _message_handshake_response : ident := $"message_handshake_response".
Definition _message_header : ident := $"message_header".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _message_macs : ident := $"message_macs".
Definition _n : ident := $"n".
Definition _net_device : ident := $"net_device".
Definition _new_device : ident := $"new_device".
Definition _new_pair : ident := $"new_pair".
Definition _new_peer : ident := $"new_peer".
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
Definition _p : ident := $"p".
Definition _pair : ident := $"pair".
Definition _peer : ident := $"peer".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _private_key : ident := $"private_key".
Definition _psk : ident := $"psk".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _public_key : ident := $"public_key".
Definition _q : ident := $"q".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiver_index : ident := $"receiver_index".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _same_peer : ident := $"same_peer".
Definition _secret : ident := $"secret".
Definition _secret_birthdate : ident := $"secret_birthdate".
Definition _secret_lock : ident := $"secret_lock".
Definition _sender_index : ident := $"sender_index".
Definition _sending : ident := $"sending".
Definition _sending_counter : ident := $"sending_counter".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _to : ident := $"to".
Definition _type : ident := $"type".
Definition _unencrypted_ephemeral : ident := $"unencrypted_ephemeral".
Definition _unused : ident := $"unused".
Definition _wg : ident := $"wg".
Definition _wg_device : ident := $"wg_device".
Definition _wg_noise_handshake_consume_initiation : ident := $"wg_noise_handshake_consume_initiation".
Definition _wg_noise_handshake_consume_response : ident := $"wg_noise_handshake_consume_response".
Definition _wg_noise_handshake_create_initiation : ident := $"wg_noise_handshake_create_initiation".
Definition _wg_noise_handshake_create_response : ident := $"wg_noise_handshake_create_response".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_init : ident := $"wg_noise_init".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
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
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition f_any_u64 := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_high, tulong) :: (_t'2, tuint) :: (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sset _high (Ecast (Etempvar _t'1 tuint) tulong)))
  (Ssequence
    (Scall (Some _t'2) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sreturn (Some (Ebinop Oor
                     (Ebinop Oshl (Etempvar _high tulong)
                       (Econst_int (Int.repr 32) tint) tulong)
                     (Etempvar _t'2 tuint) tulong)))))
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

Definition f_any_clocks := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'3, tuint) :: (_t'2, tulong) :: (_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _any_u64 (Tfunction nil tulong cc_default)) nil)
    (Sassign (Evar _wg_shim_boottime_ns tulong)
      (Ebinop Oshr (Etempvar _t'1 tulong) (Econst_int (Int.repr 2) tint)
        tulong)))
  (Ssequence
    (Ssequence
      (Scall (Some _t'2) (Evar _any_u64 (Tfunction nil tulong cc_default))
        nil)
      (Sassign (Evar _wg_shim_real_sec tlong)
        (Ecast (Etempvar _t'2 tulong) tlong)))
    (Ssequence
      (Scall (Some _t'3) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
        nil)
      (Sassign (Evar _wg_shim_real_nsec tlong)
        (Ecast
          (Ebinop Omod (Etempvar _t'3 tuint)
            (Econst_int (Int.repr 1000000000) tuint) tuint) tlong)))))
|}.

Definition f_new_device := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_wg, (tptr (Tstruct _wg_device noattr))) ::
                (_indices, (tptr (Tstruct _index_hashtable noattr))) ::
                (_keys, (tptr (Tstruct _pubkey_hashtable noattr))) ::
                (_private_key, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign
    (Efield
      (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
        (Tstruct _wg_device noattr)) _index_hashtable
      (tptr (Tstruct _index_hashtable noattr)))
    (Etempvar _indices (tptr (Tstruct _index_hashtable noattr))))
  (Ssequence
    (Sassign
      (Efield
        (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
          (Tstruct _wg_device noattr)) _peer_hashtable
        (tptr (Tstruct _pubkey_hashtable noattr)))
      (Etempvar _keys (tptr (Tstruct _pubkey_hashtable noattr))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Etempvar _indices (tptr (Tstruct _index_hashtable noattr)))
            (Tstruct _index_hashtable noattr)) _head
          (tptr (Tstruct _index_hashtable_entry noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _keys (tptr (Tstruct _pubkey_hashtable noattr)))
              (Tstruct _pubkey_hashtable noattr)) _head
            (tptr (Tstruct _wg_peer noattr)))
          (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
        (Ssequence
          (Ssequence
            (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
            (Sloop
              (Ssequence
                (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                               (Econst_int (Int.repr 32) tint) tint)
                  Sskip
                  Sbreak)
                (Sassign
                  (Ederef
                    (Ebinop Oadd
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                            (Tstruct _wg_device noattr)) _static_identity
                          (Tstruct _noise_static_identity noattr))
                        _static_public (tarray tuchar 32))
                      (Etempvar _i tulong) (tptr tuchar)) tuchar)
                  (Econst_int (Int.repr 0) tint)))
              (Sset _i
                (Ebinop Oadd (Etempvar _i tulong)
                  (Econst_int (Int.repr 1) tint) tulong))))
          (Scall None
            (Evar _wg_noise_set_static_identity_private_key (Tfunction
                                                              ((tptr (Tstruct _noise_static_identity noattr)) ::
                                                               (tptr tuchar) ::
                                                               nil) tvoid
                                                              cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                   (Tstruct _wg_device noattr)) _static_identity
                 (Tstruct _noise_static_identity noattr))
               (tptr (Tstruct _noise_static_identity noattr))) ::
             (Etempvar _private_key (tptr tuchar)) :: nil)))))))
|}.

Definition f_new_peer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) ::
                (_wg, (tptr (Tstruct _wg_device noattr))) ::
                (_public_key, (tptr tuchar)) :: (_psk, (tptr tuchar)) :: nil);
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
                    (Tstruct _wg_peer noattr)) _refcount
                  (Tstruct _kref noattr)) _refcount tuint)
              (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall None
                (Evar _wg_noise_handshake_init (Tfunction
                                                 ((tptr (Tstruct _noise_handshake noattr)) ::
                                                  (tptr (Tstruct _noise_static_identity noattr)) ::
                                                  (tptr tuchar) ::
                                                  (tptr tuchar) ::
                                                  (tptr (Tstruct _wg_peer noattr)) ::
                                                  nil) tvoid cc_default))
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
                 (Etempvar _public_key (tptr tuchar)) ::
                 (Etempvar _psk (tptr tuchar)) ::
                 (Etempvar _peer (tptr (Tstruct _wg_peer noattr))) :: nil))
              (Ssequence
                (Ssequence
                  (Sset _t'2
                    (Efield
                      (Ederef
                        (Etempvar _wg (tptr (Tstruct _wg_device noattr)))
                        (Tstruct _wg_device noattr)) _peer_hashtable
                      (tptr (Tstruct _pubkey_hashtable noattr))))
                  (Ssequence
                    (Sset _t'3
                      (Efield
                        (Ederef
                          (Etempvar _t'2 (tptr (Tstruct _pubkey_hashtable noattr)))
                          (Tstruct _pubkey_hashtable noattr)) _head
                        (tptr (Tstruct _wg_peer noattr))))
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
                        (Tstruct _wg_device noattr)) _peer_hashtable
                      (tptr (Tstruct _pubkey_hashtable noattr))))
                  (Sassign
                    (Efield
                      (Ederef
                        (Etempvar _t'1 (tptr (Tstruct _pubkey_hashtable noattr)))
                        (Tstruct _pubkey_hashtable noattr)) _head
                      (tptr (Tstruct _wg_peer noattr)))
                    (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))))))))))))
|}.

Definition f_new_pair := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _pair noattr))) :: nil);
  fn_vars := ((_a_private, (tarray tuchar 32)) ::
              (_b_private, (tarray tuchar 32)) ::
              (_psk, (tarray tuchar 32)) :: nil);
  fn_temps := nil;
  fn_body :=
(Ssequence
  (Scall None
    (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                          cc_default))
    ((Evar _a_private (tarray tuchar 32)) ::
     (Econst_int (Int.repr 32) tint) :: nil))
  (Ssequence
    (Scall None
      (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
      ((Evar _b_private (tarray tuchar 32)) ::
       (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Evar _psk (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
         nil))
      (Ssequence
        (Scall None (Evar _wg_noise_init (Tfunction nil tvoid cc_default))
          nil)
        (Ssequence
          (Scall None
            (Evar _new_device (Tfunction
                                ((tptr (Tstruct _wg_device noattr)) ::
                                 (tptr (Tstruct _index_hashtable noattr)) ::
                                 (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                 (tptr tuchar) :: nil) tvoid cc_default))
            ((Eaddrof
               (Efield
                 (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                   (Tstruct _pair noattr)) _a (Tstruct _wg_device noattr))
               (tptr (Tstruct _wg_device noattr))) ::
             (Eaddrof
               (Efield
                 (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                   (Tstruct _pair noattr)) _a_indices
                 (Tstruct _index_hashtable noattr))
               (tptr (Tstruct _index_hashtable noattr))) ::
             (Eaddrof
               (Efield
                 (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                   (Tstruct _pair noattr)) _a_keys
                 (Tstruct _pubkey_hashtable noattr))
               (tptr (Tstruct _pubkey_hashtable noattr))) ::
             (Evar _a_private (tarray tuchar 32)) :: nil))
          (Ssequence
            (Scall None
              (Evar _new_device (Tfunction
                                  ((tptr (Tstruct _wg_device noattr)) ::
                                   (tptr (Tstruct _index_hashtable noattr)) ::
                                   (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
              ((Eaddrof
                 (Efield
                   (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                     (Tstruct _pair noattr)) _b (Tstruct _wg_device noattr))
                 (tptr (Tstruct _wg_device noattr))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                     (Tstruct _pair noattr)) _b_indices
                   (Tstruct _index_hashtable noattr))
                 (tptr (Tstruct _index_hashtable noattr))) ::
               (Eaddrof
                 (Efield
                   (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                     (Tstruct _pair noattr)) _b_keys
                   (Tstruct _pubkey_hashtable noattr))
                 (tptr (Tstruct _pubkey_hashtable noattr))) ::
               (Evar _b_private (tarray tuchar 32)) :: nil))
            (Ssequence
              (Scall None
                (Evar _new_peer (Tfunction
                                  ((tptr (Tstruct _wg_peer noattr)) ::
                                   (tptr (Tstruct _wg_device noattr)) ::
                                   (tptr tuchar) :: (tptr tuchar) :: nil)
                                  tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                       (Tstruct _pair noattr)) _a_peer
                     (Tstruct _wg_peer noattr))
                   (tptr (Tstruct _wg_peer noattr))) ::
                 (Eaddrof
                   (Efield
                     (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                       (Tstruct _pair noattr)) _a
                     (Tstruct _wg_device noattr))
                   (tptr (Tstruct _wg_device noattr))) ::
                 (Efield
                   (Efield
                     (Efield
                       (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                         (Tstruct _pair noattr)) _b
                       (Tstruct _wg_device noattr)) _static_identity
                     (Tstruct _noise_static_identity noattr)) _static_public
                   (tarray tuchar 32)) :: (Evar _psk (tarray tuchar 32)) ::
                 nil))
              (Scall None
                (Evar _new_peer (Tfunction
                                  ((tptr (Tstruct _wg_peer noattr)) ::
                                   (tptr (Tstruct _wg_device noattr)) ::
                                   (tptr tuchar) :: (tptr tuchar) :: nil)
                                  tvoid cc_default))
                ((Eaddrof
                   (Efield
                     (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                       (Tstruct _pair noattr)) _b_peer
                     (Tstruct _wg_peer noattr))
                   (tptr (Tstruct _wg_peer noattr))) ::
                 (Eaddrof
                   (Efield
                     (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                       (Tstruct _pair noattr)) _b
                     (Tstruct _wg_device noattr))
                   (tptr (Tstruct _wg_device noattr))) ::
                 (Efield
                   (Efield
                     (Efield
                       (Ederef (Etempvar _p (tptr (Tstruct _pair noattr)))
                         (Tstruct _pair noattr)) _a
                       (Tstruct _wg_device noattr)) _static_identity
                     (Tstruct _noise_static_identity noattr)) _static_public
                   (tarray tuchar 32)) :: (Evar _psk (tarray tuchar 32)) ::
                 nil)))))))))
|}.

Definition f_copy_peer := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_to, (tptr (Tstruct _wg_peer noattr))) ::
                (_from, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_h, (tptr (Tstruct _noise_handshake noattr))) ::
               (_i, tulong) :: (_t'21, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'20, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'19, tbool) :: (_t'18, tint) :: (_t'17, tuint) ::
               (_t'16, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'15, tint) :: (_t'14, tulong) :: (_t'13, tuint) ::
               (_t'12, tuchar) :: (_t'11, tuchar) :: (_t'10, tuchar) ::
               (_t'9, tuchar) :: (_t'8, tuchar) :: (_t'7, tuchar) ::
               (_t'6, tuchar) :: (_t'5, tuchar) ::
               (_t'4, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'3, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'2, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _h
    (Eaddrof
      (Efield
        (Ederef (Etempvar _from (tptr (Tstruct _wg_peer noattr)))
          (Tstruct _wg_peer noattr)) _handshake
        (Tstruct _noise_handshake noattr))
      (tptr (Tstruct _noise_handshake noattr))))
  (Ssequence
    (Ssequence
      (Sset _t'21
        (Efield
          (Efield
            (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
              (Tstruct _noise_handshake noattr)) _entry
            (Tstruct _index_hashtable_entry noattr)) _peer
          (tptr (Tstruct _wg_peer noattr))))
      (Sassign
        (Efield
          (Efield
            (Efield
              (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                (Tstruct _wg_peer noattr)) _handshake
              (Tstruct _noise_handshake noattr)) _entry
            (Tstruct _index_hashtable_entry noattr)) _peer
          (tptr (Tstruct _wg_peer noattr)))
        (Etempvar _t'21 (tptr (Tstruct _wg_peer noattr)))))
    (Ssequence
      (Ssequence
        (Sset _t'20
          (Efield
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _entry
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr))))
        (Sassign
          (Efield
            (Efield
              (Efield
                (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                  (Tstruct _wg_peer noattr)) _handshake
                (Tstruct _noise_handshake noattr)) _entry
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr)))
          (Etempvar _t'20 (tptr (Tstruct _index_hashtable_entry noattr)))))
      (Ssequence
        (Ssequence
          (Sset _t'19
            (Efield
              (Efield
                (Ederef
                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                  (Tstruct _noise_handshake noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
          (Sassign
            (Efield
              (Efield
                (Efield
                  (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _handshake
                  (Tstruct _noise_handshake noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _hashed tbool)
            (Etempvar _t'19 tbool)))
        (Ssequence
          (Ssequence
            (Sset _t'18
              (Efield
                (Efield
                  (Ederef
                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                    (Tstruct _noise_handshake noattr)) _entry
                  (Tstruct _index_hashtable_entry noattr)) _type tint))
            (Sassign
              (Efield
                (Efield
                  (Efield
                    (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _handshake
                    (Tstruct _noise_handshake noattr)) _entry
                  (Tstruct _index_hashtable_entry noattr)) _type tint)
              (Etempvar _t'18 tint)))
          (Ssequence
            (Ssequence
              (Sset _t'17
                (Efield
                  (Efield
                    (Ederef
                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _entry
                    (Tstruct _index_hashtable_entry noattr)) _index tuint))
              (Sassign
                (Efield
                  (Efield
                    (Efield
                      (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _handshake
                      (Tstruct _noise_handshake noattr)) _entry
                    (Tstruct _index_hashtable_entry noattr)) _index tuint)
                (Etempvar _t'17 tuint)))
            (Ssequence
              (Ssequence
                (Sset _t'16
                  (Efield
                    (Ederef
                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _static_identity
                    (tptr (Tstruct _noise_static_identity noattr))))
                (Sassign
                  (Efield
                    (Efield
                      (Ederef (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _handshake
                      (Tstruct _noise_handshake noattr)) _static_identity
                    (tptr (Tstruct _noise_static_identity noattr)))
                  (Etempvar _t'16 (tptr (Tstruct _noise_static_identity noattr)))))
              (Ssequence
                (Ssequence
                  (Sset _t'15
                    (Efield
                      (Ederef
                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                        (Tstruct _noise_handshake noattr)) _state tint))
                  (Sassign
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                          (Tstruct _wg_peer noattr)) _handshake
                        (Tstruct _noise_handshake noattr)) _state tint)
                    (Etempvar _t'15 tint)))
                (Ssequence
                  (Ssequence
                    (Sset _t'14
                      (Efield
                        (Ederef
                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                          (Tstruct _noise_handshake noattr))
                        _last_initiation_consumption tulong))
                    (Sassign
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _handshake
                          (Tstruct _noise_handshake noattr))
                        _last_initiation_consumption tulong)
                      (Etempvar _t'14 tulong)))
                  (Ssequence
                    (Ssequence
                      (Sset _t'13
                        (Efield
                          (Ederef
                            (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                            (Tstruct _noise_handshake noattr)) _remote_index
                          tuint))
                      (Sassign
                        (Efield
                          (Efield
                            (Ederef
                              (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                              (Tstruct _wg_peer noattr)) _handshake
                            (Tstruct _noise_handshake noattr)) _remote_index
                          tuint) (Etempvar _t'13 tuint)))
                    (Ssequence
                      (Ssequence
                        (Sset _i
                          (Ecast (Econst_int (Int.repr 0) tint) tulong))
                        (Sloop
                          (Ssequence
                            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                                           (Econst_int (Int.repr 32) tint)
                                           tint)
                              Sskip
                              Sbreak)
                            (Ssequence
                              (Ssequence
                                (Sset _t'12
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _ephemeral_private
                                        (tarray tuchar 32))
                                      (Etempvar _i tulong) (tptr tuchar))
                                    tuchar))
                                (Sassign
                                  (Ederef
                                    (Ebinop Oadd
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                            (Tstruct _wg_peer noattr))
                                          _handshake
                                          (Tstruct _noise_handshake noattr))
                                        _ephemeral_private
                                        (tarray tuchar 32))
                                      (Etempvar _i tulong) (tptr tuchar))
                                    tuchar) (Etempvar _t'12 tuchar)))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'11
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Ederef
                                            (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _remote_static (tarray tuchar 32))
                                        (Etempvar _i tulong) (tptr tuchar))
                                      tuchar))
                                  (Sassign
                                    (Ederef
                                      (Ebinop Oadd
                                        (Efield
                                          (Efield
                                            (Ederef
                                              (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                              (Tstruct _wg_peer noattr))
                                            _handshake
                                            (Tstruct _noise_handshake noattr))
                                          _remote_static (tarray tuchar 32))
                                        (Etempvar _i tulong) (tptr tuchar))
                                      tuchar) (Etempvar _t'11 tuchar)))
                                (Ssequence
                                  (Ssequence
                                    (Sset _t'10
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Ederef
                                              (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                              (Tstruct _noise_handshake noattr))
                                            _remote_ephemeral
                                            (tarray tuchar 32))
                                          (Etempvar _i tulong) (tptr tuchar))
                                        tuchar))
                                    (Sassign
                                      (Ederef
                                        (Ebinop Oadd
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                (Tstruct _wg_peer noattr))
                                              _handshake
                                              (Tstruct _noise_handshake noattr))
                                            _remote_ephemeral
                                            (tarray tuchar 32))
                                          (Etempvar _i tulong) (tptr tuchar))
                                        tuchar) (Etempvar _t'10 tuchar)))
                                  (Ssequence
                                    (Ssequence
                                      (Sset _t'9
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Ederef
                                                (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                (Tstruct _noise_handshake noattr))
                                              _precomputed_static_static
                                              (tarray tuchar 32))
                                            (Etempvar _i tulong)
                                            (tptr tuchar)) tuchar))
                                      (Sassign
                                        (Ederef
                                          (Ebinop Oadd
                                            (Efield
                                              (Efield
                                                (Ederef
                                                  (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                  (Tstruct _wg_peer noattr))
                                                _handshake
                                                (Tstruct _noise_handshake noattr))
                                              _precomputed_static_static
                                              (tarray tuchar 32))
                                            (Etempvar _i tulong)
                                            (tptr tuchar)) tuchar)
                                        (Etempvar _t'9 tuchar)))
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'8
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Ederef
                                                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                  (Tstruct _noise_handshake noattr))
                                                _preshared_key
                                                (tarray tuchar 32))
                                              (Etempvar _i tulong)
                                              (tptr tuchar)) tuchar))
                                        (Sassign
                                          (Ederef
                                            (Ebinop Oadd
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                    (Tstruct _wg_peer noattr))
                                                  _handshake
                                                  (Tstruct _noise_handshake noattr))
                                                _preshared_key
                                                (tarray tuchar 32))
                                              (Etempvar _i tulong)
                                              (tptr tuchar)) tuchar)
                                          (Etempvar _t'8 tuchar)))
                                      (Ssequence
                                        (Ssequence
                                          (Sset _t'7
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                    (Tstruct _noise_handshake noattr))
                                                  _hash (tarray tuchar 32))
                                                (Etempvar _i tulong)
                                                (tptr tuchar)) tuchar))
                                          (Sassign
                                            (Ederef
                                              (Ebinop Oadd
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                      (Tstruct _wg_peer noattr))
                                                    _handshake
                                                    (Tstruct _noise_handshake noattr))
                                                  _hash (tarray tuchar 32))
                                                (Etempvar _i tulong)
                                                (tptr tuchar)) tuchar)
                                            (Etempvar _t'7 tuchar)))
                                        (Ssequence
                                          (Ssequence
                                            (Sset _t'6
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _chaining_key
                                                    (tarray tuchar 32))
                                                  (Etempvar _i tulong)
                                                  (tptr tuchar)) tuchar))
                                            (Sassign
                                              (Ederef
                                                (Ebinop Oadd
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                        (Tstruct _wg_peer noattr))
                                                      _handshake
                                                      (Tstruct _noise_handshake noattr))
                                                    _chaining_key
                                                    (tarray tuchar 32))
                                                  (Etempvar _i tulong)
                                                  (tptr tuchar)) tuchar)
                                              (Etempvar _t'6 tuchar)))
                                          (Sifthenelse (Ebinop Olt
                                                         (Etempvar _i tulong)
                                                         (Econst_int (Int.repr 12) tint)
                                                         tint)
                                            (Ssequence
                                              (Sset _t'5
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _latest_timestamp
                                                      (tarray tuchar 12))
                                                    (Etempvar _i tulong)
                                                    (tptr tuchar)) tuchar))
                                              (Sassign
                                                (Ederef
                                                  (Ebinop Oadd
                                                    (Efield
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                                          (Tstruct _wg_peer noattr))
                                                        _handshake
                                                        (Tstruct _noise_handshake noattr))
                                                      _latest_timestamp
                                                      (tarray tuchar 12))
                                                    (Etempvar _i tulong)
                                                    (tptr tuchar)) tuchar)
                                                (Etempvar _t'5 tuchar)))
                                            Sskip)))))))))
                          (Sset _i
                            (Ebinop Oadd (Etempvar _i tulong)
                              (Econst_int (Int.repr 1) tint) tulong))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'4
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _from (tptr (Tstruct _wg_peer noattr)))
                                  (Tstruct _wg_peer noattr)) _keypairs
                                (Tstruct _noise_keypairs noattr))
                              _current_keypair
                              (tptr (Tstruct _noise_keypair noattr))))
                          (Sassign
                            (Efield
                              (Efield
                                (Ederef
                                  (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                  (Tstruct _wg_peer noattr)) _keypairs
                                (Tstruct _noise_keypairs noattr))
                              _current_keypair
                              (tptr (Tstruct _noise_keypair noattr)))
                            (Etempvar _t'4 (tptr (Tstruct _noise_keypair noattr)))))
                        (Ssequence
                          (Ssequence
                            (Sset _t'3
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _from (tptr (Tstruct _wg_peer noattr)))
                                    (Tstruct _wg_peer noattr)) _keypairs
                                  (Tstruct _noise_keypairs noattr))
                                _previous_keypair
                                (tptr (Tstruct _noise_keypair noattr))))
                            (Sassign
                              (Efield
                                (Efield
                                  (Ederef
                                    (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                    (Tstruct _wg_peer noattr)) _keypairs
                                  (Tstruct _noise_keypairs noattr))
                                _previous_keypair
                                (tptr (Tstruct _noise_keypair noattr)))
                              (Etempvar _t'3 (tptr (Tstruct _noise_keypair noattr)))))
                          (Ssequence
                            (Ssequence
                              (Sset _t'2
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _from (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _keypairs
                                    (Tstruct _noise_keypairs noattr))
                                  _next_keypair
                                  (tptr (Tstruct _noise_keypair noattr))))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _keypairs
                                    (Tstruct _noise_keypairs noattr))
                                  _next_keypair
                                  (tptr (Tstruct _noise_keypair noattr)))
                                (Etempvar _t'2 (tptr (Tstruct _noise_keypair noattr)))))
                            (Ssequence
                              (Sset _t'1
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _from (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _refcount
                                    (Tstruct _kref noattr)) _refcount tuint))
                              (Sassign
                                (Efield
                                  (Efield
                                    (Ederef
                                      (Etempvar _to (tptr (Tstruct _wg_peer noattr)))
                                      (Tstruct _wg_peer noattr)) _refcount
                                    (Tstruct _kref noattr)) _refcount tuint)
                                (Etempvar _t'1 tuint)))))))))))))))))
|}.

Definition f_same_peer := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr (Tstruct _wg_peer noattr))) ::
                (_q, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_a, (tptr (Tstruct _noise_handshake noattr))) ::
               (_b, (tptr (Tstruct _noise_handshake noattr))) ::
               (_t'28, tint) :: (_t'27, tint) :: (_t'26, tint) ::
               (_t'25, tint) :: (_t'24, tint) :: (_t'23, tint) ::
               (_t'22, tint) :: (_t'21, tint) :: (_t'20, tint) ::
               (_t'19, tint) :: (_t'18, tint) :: (_t'17, tint) ::
               (_t'16, tint) :: (_t'15, tint) :: (_t'14, tint) ::
               (_t'13, tint) :: (_t'12, tint) :: (_t'11, tint) ::
               (_t'10, tint) :: (_t'9, tint) :: (_t'8, tint) ::
               (_t'7, tint) :: (_t'6, tint) :: (_t'5, tint) ::
               (_t'4, tint) :: (_t'3, tint) :: (_t'2, tint) ::
               (_t'1, tint) ::
               (_t'54, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'53, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'52, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'51, (tptr (Tstruct _wg_peer noattr))) :: (_t'50, tbool) ::
               (_t'49, tbool) :: (_t'48, tint) :: (_t'47, tint) ::
               (_t'46, tuint) :: (_t'45, tuint) ::
               (_t'44, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'43, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'42, tint) :: (_t'41, tint) :: (_t'40, tuint) ::
               (_t'39, tuint) :: (_t'38, tulong) :: (_t'37, tulong) ::
               (_t'36, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'35, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'34, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'33, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'32, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'31, (tptr (Tstruct _noise_keypair noattr))) ::
               (_t'30, tuint) :: (_t'29, tuint) :: nil);
  fn_body :=
(Ssequence
  (Sset _a
    (Eaddrof
      (Efield
        (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
          (Tstruct _wg_peer noattr)) _handshake
        (Tstruct _noise_handshake noattr))
      (tptr (Tstruct _noise_handshake noattr))))
  (Ssequence
    (Sset _b
      (Eaddrof
        (Efield
          (Ederef (Etempvar _q (tptr (Tstruct _wg_peer noattr)))
            (Tstruct _wg_peer noattr)) _handshake
          (Tstruct _noise_handshake noattr))
        (tptr (Tstruct _noise_handshake noattr))))
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
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'51
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _peer
                                                  (tptr (Tstruct _wg_peer noattr))))
                                              (Ssequence
                                                (Sset _t'52
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _entry
                                                      (Tstruct _index_hashtable_entry noattr))
                                                    _peer
                                                    (tptr (Tstruct _wg_peer noattr))))
                                                (Sifthenelse (Ebinop Oeq
                                                               (Etempvar _t'51 (tptr (Tstruct _wg_peer noattr)))
                                                               (Etempvar _t'52 (tptr (Tstruct _wg_peer noattr)))
                                                               tint)
                                                  (Ssequence
                                                    (Sset _t'53
                                                      (Efield
                                                        (Efield
                                                          (Ederef
                                                            (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                            (Tstruct _noise_handshake noattr))
                                                          _entry
                                                          (Tstruct _index_hashtable_entry noattr))
                                                        _next
                                                        (tptr (Tstruct _index_hashtable_entry noattr))))
                                                    (Ssequence
                                                      (Sset _t'54
                                                        (Efield
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                              (Tstruct _noise_handshake noattr))
                                                            _entry
                                                            (Tstruct _index_hashtable_entry noattr))
                                                          _next
                                                          (tptr (Tstruct _index_hashtable_entry noattr))))
                                                      (Sset _t'1
                                                        (Ecast
                                                          (Ebinop Oeq
                                                            (Etempvar _t'53 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                            (Etempvar _t'54 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                            tint) tbool))))
                                                  (Sset _t'1
                                                    (Econst_int (Int.repr 0) tint)))))
                                            (Sifthenelse (Etempvar _t'1 tint)
                                              (Ssequence
                                                (Sset _t'49
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _entry
                                                      (Tstruct _index_hashtable_entry noattr))
                                                    _hashed tbool))
                                                (Ssequence
                                                  (Sset _t'50
                                                    (Efield
                                                      (Efield
                                                        (Ederef
                                                          (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                          (Tstruct _noise_handshake noattr))
                                                        _entry
                                                        (Tstruct _index_hashtable_entry noattr))
                                                      _hashed tbool))
                                                  (Sset _t'2
                                                    (Ecast
                                                      (Ebinop Oeq
                                                        (Etempvar _t'49 tbool)
                                                        (Etempvar _t'50 tbool)
                                                        tint) tbool))))
                                              (Sset _t'2
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'2 tint)
                                            (Ssequence
                                              (Sset _t'47
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _type tint))
                                              (Ssequence
                                                (Sset _t'48
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _entry
                                                      (Tstruct _index_hashtable_entry noattr))
                                                    _type tint))
                                                (Sset _t'3
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _t'47 tint)
                                                      (Etempvar _t'48 tint)
                                                      tint) tbool))))
                                            (Sset _t'3
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Etempvar _t'3 tint)
                                          (Ssequence
                                            (Sset _t'45
                                              (Efield
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                    (Tstruct _noise_handshake noattr))
                                                  _entry
                                                  (Tstruct _index_hashtable_entry noattr))
                                                _index tuint))
                                            (Ssequence
                                              (Sset _t'46
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _index tuint))
                                              (Sset _t'4
                                                (Ecast
                                                  (Ebinop Oeq
                                                    (Etempvar _t'45 tuint)
                                                    (Etempvar _t'46 tuint)
                                                    tint) tbool))))
                                          (Sset _t'4
                                            (Econst_int (Int.repr 0) tint))))
                                      (Sifthenelse (Etempvar _t'4 tint)
                                        (Ssequence
                                          (Sset _t'43
                                            (Efield
                                              (Ederef
                                                (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                                (Tstruct _noise_handshake noattr))
                                              _static_identity
                                              (tptr (Tstruct _noise_static_identity noattr))))
                                          (Ssequence
                                            (Sset _t'44
                                              (Efield
                                                (Ederef
                                                  (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                  (Tstruct _noise_handshake noattr))
                                                _static_identity
                                                (tptr (Tstruct _noise_static_identity noattr))))
                                            (Sset _t'5
                                              (Ecast
                                                (Ebinop Oeq
                                                  (Etempvar _t'43 (tptr (Tstruct _noise_static_identity noattr)))
                                                  (Etempvar _t'44 (tptr (Tstruct _noise_static_identity noattr)))
                                                  tint) tbool))))
                                        (Sset _t'5
                                          (Econst_int (Int.repr 0) tint))))
                                    (Sifthenelse (Etempvar _t'5 tint)
                                      (Ssequence
                                        (Sset _t'41
                                          (Efield
                                            (Ederef
                                              (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                              (Tstruct _noise_handshake noattr))
                                            _state tint))
                                        (Ssequence
                                          (Sset _t'42
                                            (Efield
                                              (Ederef
                                                (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                                (Tstruct _noise_handshake noattr))
                                              _state tint))
                                          (Sset _t'6
                                            (Ecast
                                              (Ebinop Oeq
                                                (Etempvar _t'41 tint)
                                                (Etempvar _t'42 tint) tint)
                                              tbool))))
                                      (Sset _t'6
                                        (Econst_int (Int.repr 0) tint))))
                                  (Sifthenelse (Etempvar _t'6 tint)
                                    (Ssequence
                                      (Sset _t'39
                                        (Efield
                                          (Ederef
                                            (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _remote_index tuint))
                                      (Ssequence
                                        (Sset _t'40
                                          (Efield
                                            (Ederef
                                              (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                              (Tstruct _noise_handshake noattr))
                                            _remote_index tuint))
                                        (Sset _t'7
                                          (Ecast
                                            (Ebinop Oeq
                                              (Etempvar _t'39 tuint)
                                              (Etempvar _t'40 tuint) tint)
                                            tbool))))
                                    (Sset _t'7
                                      (Econst_int (Int.repr 0) tint))))
                                (Sifthenelse (Etempvar _t'7 tint)
                                  (Ssequence
                                    (Sset _t'37
                                      (Efield
                                        (Ederef
                                          (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _last_initiation_consumption tulong))
                                    (Ssequence
                                      (Sset _t'38
                                        (Efield
                                          (Ederef
                                            (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _last_initiation_consumption
                                          tulong))
                                      (Sset _t'8
                                        (Ecast
                                          (Ebinop Oeq (Etempvar _t'37 tulong)
                                            (Etempvar _t'38 tulong) tint)
                                          tbool))))
                                  (Sset _t'8 (Econst_int (Int.repr 0) tint))))
                              (Sifthenelse (Etempvar _t'8 tint)
                                (Ssequence
                                  (Scall (Some _t'10)
                                    (Evar _bytes_eq (Tfunction
                                                      ((tptr tuchar) ::
                                                       (tptr tuchar) ::
                                                       tulong :: nil) tint
                                                      cc_default))
                                    ((Efield
                                       (Ederef
                                         (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                         (Tstruct _noise_handshake noattr))
                                       _ephemeral_private (tarray tuchar 32)) ::
                                     (Efield
                                       (Ederef
                                         (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                         (Tstruct _noise_handshake noattr))
                                       _ephemeral_private (tarray tuchar 32)) ::
                                     (Econst_int (Int.repr 32) tint) :: nil))
                                  (Sset _t'9
                                    (Ecast (Etempvar _t'10 tint) tbool)))
                                (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'9 tint)
                              (Ssequence
                                (Scall (Some _t'12)
                                  (Evar _bytes_eq (Tfunction
                                                    ((tptr tuchar) ::
                                                     (tptr tuchar) ::
                                                     tulong :: nil) tint
                                                    cc_default))
                                  ((Efield
                                     (Ederef
                                       (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                       (Tstruct _noise_handshake noattr))
                                     _remote_static (tarray tuchar 32)) ::
                                   (Efield
                                     (Ederef
                                       (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                       (Tstruct _noise_handshake noattr))
                                     _remote_static (tarray tuchar 32)) ::
                                   (Econst_int (Int.repr 32) tint) :: nil))
                                (Sset _t'11
                                  (Ecast (Etempvar _t'12 tint) tbool)))
                              (Sset _t'11 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'11 tint)
                            (Ssequence
                              (Scall (Some _t'14)
                                (Evar _bytes_eq (Tfunction
                                                  ((tptr tuchar) ::
                                                   (tptr tuchar) :: tulong ::
                                                   nil) tint cc_default))
                                ((Efield
                                   (Ederef
                                     (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                     (Tstruct _noise_handshake noattr))
                                   _remote_ephemeral (tarray tuchar 32)) ::
                                 (Efield
                                   (Ederef
                                     (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                     (Tstruct _noise_handshake noattr))
                                   _remote_ephemeral (tarray tuchar 32)) ::
                                 (Econst_int (Int.repr 32) tint) :: nil))
                              (Sset _t'13
                                (Ecast (Etempvar _t'14 tint) tbool)))
                            (Sset _t'13 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'13 tint)
                          (Ssequence
                            (Scall (Some _t'16)
                              (Evar _bytes_eq (Tfunction
                                                ((tptr tuchar) ::
                                                 (tptr tuchar) :: tulong ::
                                                 nil) tint cc_default))
                              ((Efield
                                 (Ederef
                                   (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr)) _hash
                                 (tarray tuchar 32)) ::
                               (Efield
                                 (Ederef
                                   (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                   (Tstruct _noise_handshake noattr)) _hash
                                 (tarray tuchar 32)) ::
                               (Econst_int (Int.repr 32) tint) :: nil))
                            (Sset _t'15 (Ecast (Etempvar _t'16 tint) tbool)))
                          (Sset _t'15 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'15 tint)
                        (Ssequence
                          (Scall (Some _t'18)
                            (Evar _bytes_eq (Tfunction
                                              ((tptr tuchar) ::
                                               (tptr tuchar) :: tulong ::
                                               nil) tint cc_default))
                            ((Efield
                               (Ederef
                                 (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _precomputed_static_static (tarray tuchar 32)) ::
                             (Efield
                               (Ederef
                                 (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                                 (Tstruct _noise_handshake noattr))
                               _precomputed_static_static (tarray tuchar 32)) ::
                             (Econst_int (Int.repr 32) tint) :: nil))
                          (Sset _t'17 (Ecast (Etempvar _t'18 tint) tbool)))
                        (Sset _t'17 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'17 tint)
                      (Ssequence
                        (Scall (Some _t'20)
                          (Evar _bytes_eq (Tfunction
                                            ((tptr tuchar) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            tint cc_default))
                          ((Efield
                             (Ederef
                               (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _preshared_key (tarray tuchar 32)) ::
                           (Efield
                             (Ederef
                               (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                               (Tstruct _noise_handshake noattr))
                             _preshared_key (tarray tuchar 32)) ::
                           (Econst_int (Int.repr 32) tint) :: nil))
                        (Sset _t'19 (Ecast (Etempvar _t'20 tint) tbool)))
                      (Sset _t'19 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'19 tint)
                    (Ssequence
                      (Scall (Some _t'22)
                        (Evar _bytes_eq (Tfunction
                                          ((tptr tuchar) :: (tptr tuchar) ::
                                           tulong :: nil) tint cc_default))
                        ((Efield
                           (Ederef
                             (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) ::
                         (Efield
                           (Ederef
                             (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                             (Tstruct _noise_handshake noattr)) _chaining_key
                           (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Sset _t'21 (Ecast (Etempvar _t'22 tint) tbool)))
                    (Sset _t'21 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'21 tint)
                  (Ssequence
                    (Scall (Some _t'24)
                      (Evar _bytes_eq (Tfunction
                                        ((tptr tuchar) :: (tptr tuchar) ::
                                         tulong :: nil) tint cc_default))
                      ((Efield
                         (Ederef
                           (Etempvar _a (tptr (Tstruct _noise_handshake noattr)))
                           (Tstruct _noise_handshake noattr))
                         _latest_timestamp (tarray tuchar 12)) ::
                       (Efield
                         (Ederef
                           (Etempvar _b (tptr (Tstruct _noise_handshake noattr)))
                           (Tstruct _noise_handshake noattr))
                         _latest_timestamp (tarray tuchar 12)) ::
                       (Econst_int (Int.repr 12) tint) :: nil))
                    (Sset _t'23 (Ecast (Etempvar _t'24 tint) tbool)))
                  (Sset _t'23 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'23 tint)
                (Ssequence
                  (Sset _t'35
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                          (Tstruct _wg_peer noattr)) _keypairs
                        (Tstruct _noise_keypairs noattr)) _current_keypair
                      (tptr (Tstruct _noise_keypair noattr))))
                  (Ssequence
                    (Sset _t'36
                      (Efield
                        (Efield
                          (Ederef
                            (Etempvar _q (tptr (Tstruct _wg_peer noattr)))
                            (Tstruct _wg_peer noattr)) _keypairs
                          (Tstruct _noise_keypairs noattr)) _current_keypair
                        (tptr (Tstruct _noise_keypair noattr))))
                    (Sset _t'25
                      (Ecast
                        (Ebinop Oeq
                          (Etempvar _t'35 (tptr (Tstruct _noise_keypair noattr)))
                          (Etempvar _t'36 (tptr (Tstruct _noise_keypair noattr)))
                          tint) tbool))))
                (Sset _t'25 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'25 tint)
              (Ssequence
                (Sset _t'33
                  (Efield
                    (Efield
                      (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _keypairs
                      (Tstruct _noise_keypairs noattr)) _previous_keypair
                    (tptr (Tstruct _noise_keypair noattr))))
                (Ssequence
                  (Sset _t'34
                    (Efield
                      (Efield
                        (Ederef
                          (Etempvar _q (tptr (Tstruct _wg_peer noattr)))
                          (Tstruct _wg_peer noattr)) _keypairs
                        (Tstruct _noise_keypairs noattr)) _previous_keypair
                      (tptr (Tstruct _noise_keypair noattr))))
                  (Sset _t'26
                    (Ecast
                      (Ebinop Oeq
                        (Etempvar _t'33 (tptr (Tstruct _noise_keypair noattr)))
                        (Etempvar _t'34 (tptr (Tstruct _noise_keypair noattr)))
                        tint) tbool))))
              (Sset _t'26 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'26 tint)
            (Ssequence
              (Sset _t'31
                (Efield
                  (Efield
                    (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _keypairs
                    (Tstruct _noise_keypairs noattr)) _next_keypair
                  (tptr (Tstruct _noise_keypair noattr))))
              (Ssequence
                (Sset _t'32
                  (Efield
                    (Efield
                      (Ederef (Etempvar _q (tptr (Tstruct _wg_peer noattr)))
                        (Tstruct _wg_peer noattr)) _keypairs
                      (Tstruct _noise_keypairs noattr)) _next_keypair
                    (tptr (Tstruct _noise_keypair noattr))))
                (Sset _t'27
                  (Ecast
                    (Ebinop Oeq
                      (Etempvar _t'31 (tptr (Tstruct _noise_keypair noattr)))
                      (Etempvar _t'32 (tptr (Tstruct _noise_keypair noattr)))
                      tint) tbool))))
            (Sset _t'27 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'27 tint)
          (Ssequence
            (Sset _t'29
              (Efield
                (Efield
                  (Ederef (Etempvar _p (tptr (Tstruct _wg_peer noattr)))
                    (Tstruct _wg_peer noattr)) _refcount
                  (Tstruct _kref noattr)) _refcount tuint))
            (Ssequence
              (Sset _t'30
                (Efield
                  (Efield
                    (Ederef (Etempvar _q (tptr (Tstruct _wg_peer noattr)))
                      (Tstruct _wg_peer noattr)) _refcount
                    (Tstruct _kref noattr)) _refcount tuint))
              (Sset _t'28
                (Ecast
                  (Ebinop Oeq (Etempvar _t'29 tuint) (Etempvar _t'30 tuint)
                    tint) tbool))))
          (Sset _t'28 (Econst_int (Int.repr 0) tint))))
      (Sreturn (Some (Etempvar _t'28 tint))))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_p, (Tstruct _pair noattr)) ::
              (_initiation, (Tstruct _message_handshake_initiation noattr)) ::
              (_message, (Tstruct _message_handshake_response noattr)) ::
              (_before, (Tstruct _wg_peer noattr)) :: nil);
  fn_temps := ((_initiated, tbool) ::
               (_found, (tptr (Tstruct _wg_peer noattr))) :: (_t'14, tint) ::
               (_t'13, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'12, tuchar) :: (_t'11, tuint) ::
               (_t'10, (tptr (Tstruct _wg_peer noattr))) :: (_t'9, tint) ::
               (_t'8, tuchar) :: (_t'7, tint) :: (_t'6, tuchar) ::
               (_t'5, tint) :: (_t'4, tuint) :: (_t'3, tuint) ::
               (_t'2, tuint) :: (_t'1, tbool) :: (_t'15, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall None
      (Evar _new_pair (Tfunction ((tptr (Tstruct _pair noattr)) :: nil) tvoid
                        cc_default))
      ((Eaddrof (Evar _p (Tstruct _pair noattr))
         (tptr (Tstruct _pair noattr))) :: nil))
    (Ssequence
      (Scall None (Evar _any_clocks (Tfunction nil tvoid cc_default)) nil)
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _wg_noise_handshake_create_initiation (Tfunction
                                                          ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                                           (tptr (Tstruct _noise_handshake noattr)) ::
                                                           nil) tbool
                                                          cc_default))
            ((Eaddrof
               (Evar _initiation (Tstruct _message_handshake_initiation noattr))
               (tptr (Tstruct _message_handshake_initiation noattr))) ::
             (Eaddrof
               (Efield
                 (Efield (Evar _p (Tstruct _pair noattr)) _a_peer
                   (Tstruct _wg_peer noattr)) _handshake
                 (Tstruct _noise_handshake noattr))
               (tptr (Tstruct _noise_handshake noattr))) :: nil))
          (Sset _initiated (Ecast (Etempvar _t'1 tbool) tbool)))
        (Ssequence
          (Ssequence
            (Scall (Some _t'2)
              (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
            (Sassign
              (Efield
                (Efield
                  (Evar _message (Tstruct _message_handshake_response noattr))
                  _header (Tstruct _message_header noattr)) _type tuint)
              (Etempvar _t'2 tuint)))
          (Ssequence
            (Ssequence
              (Scall (Some _t'3)
                (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
              (Sassign
                (Efield
                  (Evar _message (Tstruct _message_handshake_response noattr))
                  _sender_index tuint) (Etempvar _t'3 tuint)))
            (Ssequence
              (Ssequence
                (Scall (Some _t'4)
                  (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
                (Sassign
                  (Efield
                    (Evar _message (Tstruct _message_handshake_response noattr))
                    _receiver_index tuint) (Etempvar _t'4 tuint)))
              (Ssequence
                (Scall None
                  (Evar _nondet_bytes (Tfunction
                                        ((tptr tuchar) :: tulong :: nil)
                                        tvoid cc_default))
                  ((Efield
                     (Evar _message (Tstruct _message_handshake_response noattr))
                     _unencrypted_ephemeral (tarray tuchar 32)) ::
                   (Esizeof (tarray tuchar 32) tulong) :: nil))
                (Ssequence
                  (Scall None
                    (Evar _nondet_bytes (Tfunction
                                          ((tptr tuchar) :: tulong :: nil)
                                          tvoid cc_default))
                    ((Efield
                       (Evar _message (Tstruct _message_handshake_response noattr))
                       _encrypted_nothing (tarray tuchar 16)) ::
                     (Esizeof (tarray tuchar 16) tulong) :: nil))
                  (Ssequence
                    (Scall None
                      (Evar _nondet_bytes (Tfunction
                                            ((tptr tuchar) :: tulong :: nil)
                                            tvoid cc_default))
                      ((Efield
                         (Efield
                           (Evar _message (Tstruct _message_handshake_response noattr))
                           _macs (Tstruct _message_macs noattr)) _mac1
                         (tarray tuchar 16)) ::
                       (Esizeof (tarray tuchar 16) tulong) :: nil))
                    (Ssequence
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Efield
                           (Efield
                             (Evar _message (Tstruct _message_handshake_response noattr))
                             _macs (Tstruct _message_macs noattr)) _mac2
                           (tarray tuchar 16)) ::
                         (Esizeof (tarray tuchar 16) tulong) :: nil))
                      (Ssequence
                        (Ssequence
                          (Sifthenelse (Etempvar _initiated tbool)
                            (Ssequence
                              (Scall (Some _t'6)
                                (Evar _nondet_u8 (Tfunction nil tuchar
                                                   cc_default)) nil)
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oand (Etempvar _t'6 tuchar)
                                    (Econst_int (Int.repr 1) tint) tint)
                                  tbool)))
                            (Sset _t'5 (Econst_int (Int.repr 0) tint)))
                          (Sifthenelse (Etempvar _t'5 tint)
                            (Ssequence
                              (Sset _t'15
                                (Efield
                                  (Evar _initiation (Tstruct _message_handshake_initiation noattr))
                                  _sender_index tuint))
                              (Sassign
                                (Efield
                                  (Evar _message (Tstruct _message_handshake_response noattr))
                                  _receiver_index tuint)
                                (Etempvar _t'15 tuint)))
                            Sskip))
                        (Ssequence
                          (Ssequence
                            (Ssequence
                              (Sifthenelse (Etempvar _initiated tbool)
                                (Ssequence
                                  (Scall (Some _t'8)
                                    (Evar _nondet_u8 (Tfunction nil tuchar
                                                       cc_default)) nil)
                                  (Sset _t'7
                                    (Ecast
                                      (Ebinop Oand (Etempvar _t'8 tuchar)
                                        (Econst_int (Int.repr 1) tint) tint)
                                      tbool)))
                                (Sset _t'7 (Econst_int (Int.repr 0) tint)))
                              (Sifthenelse (Etempvar _t'7 tint)
                                (Ssequence
                                  (Scall (Some _t'10)
                                    (Evar _wg_noise_handshake_consume_initiation 
                                    (Tfunction
                                      ((tptr (Tstruct _message_handshake_initiation noattr)) ::
                                       (tptr (Tstruct _wg_device noattr)) ::
                                       nil) (tptr (Tstruct _wg_peer noattr))
                                      cc_default))
                                    ((Eaddrof
                                       (Evar _initiation (Tstruct _message_handshake_initiation noattr))
                                       (tptr (Tstruct _message_handshake_initiation noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Evar _p (Tstruct _pair noattr)) _b
                                         (Tstruct _wg_device noattr))
                                       (tptr (Tstruct _wg_device noattr))) ::
                                     nil))
                                  (Sset _t'9
                                    (Ecast
                                      (Ebinop One
                                        (Etempvar _t'10 (tptr (Tstruct _wg_peer noattr)))
                                        (Ecast (Econst_int (Int.repr 0) tint)
                                          (tptr tvoid)) tint) tbool)))
                                (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'9 tint)
                              (Scall None
                                (Evar _wg_noise_handshake_create_response 
                                (Tfunction
                                  ((tptr (Tstruct _message_handshake_response noattr)) ::
                                   (tptr (Tstruct _noise_handshake noattr)) ::
                                   nil) tbool cc_default))
                                ((Eaddrof
                                   (Evar _message (Tstruct _message_handshake_response noattr))
                                   (tptr (Tstruct _message_handshake_response noattr))) ::
                                 (Eaddrof
                                   (Efield
                                     (Efield (Evar _p (Tstruct _pair noattr))
                                       _b_peer (Tstruct _wg_peer noattr))
                                     _handshake
                                     (Tstruct _noise_handshake noattr))
                                   (tptr (Tstruct _noise_handshake noattr))) ::
                                 nil))
                              Sskip))
                          (Ssequence
                            (Ssequence
                              (Scall (Some _t'12)
                                (Evar _nondet_u8 (Tfunction nil tuchar
                                                   cc_default)) nil)
                              (Sifthenelse (Ebinop Oand
                                             (Etempvar _t'12 tuchar)
                                             (Econst_int (Int.repr 1) tint)
                                             tint)
                                (Ssequence
                                  (Scall (Some _t'11)
                                    (Evar _nondet_u32 (Tfunction nil tuint
                                                        cc_default)) nil)
                                  (Sassign
                                    (Efield
                                      (Efield
                                        (Efield
                                          (Evar _p (Tstruct _pair noattr))
                                          _a_peer (Tstruct _wg_peer noattr))
                                        _handshake
                                        (Tstruct _noise_handshake noattr))
                                      _state tint)
                                    (Ecast (Etempvar _t'11 tuint) tint)))
                                Sskip))
                            (Ssequence
                              (Scall None
                                (Evar _copy_peer (Tfunction
                                                   ((tptr (Tstruct _wg_peer noattr)) ::
                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                    nil) tvoid cc_default))
                                ((Eaddrof
                                   (Evar _before (Tstruct _wg_peer noattr))
                                   (tptr (Tstruct _wg_peer noattr))) ::
                                 (Eaddrof
                                   (Efield (Evar _p (Tstruct _pair noattr))
                                     _a_peer (Tstruct _wg_peer noattr))
                                   (tptr (Tstruct _wg_peer noattr))) :: nil))
                              (Ssequence
                                (Ssequence
                                  (Scall (Some _t'13)
                                    (Evar _wg_noise_handshake_consume_response 
                                    (Tfunction
                                      ((tptr (Tstruct _message_handshake_response noattr)) ::
                                       (tptr (Tstruct _wg_device noattr)) ::
                                       nil) (tptr (Tstruct _wg_peer noattr))
                                      cc_default))
                                    ((Eaddrof
                                       (Evar _message (Tstruct _message_handshake_response noattr))
                                       (tptr (Tstruct _message_handshake_response noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Evar _p (Tstruct _pair noattr)) _a
                                         (Tstruct _wg_device noattr))
                                       (tptr (Tstruct _wg_device noattr))) ::
                                     nil))
                                  (Sset _found
                                    (Etempvar _t'13 (tptr (Tstruct _wg_peer noattr)))))
                                (Ssequence
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _found (tptr (Tstruct _wg_peer noattr)))
                                                 (Ecast
                                                   (Econst_int (Int.repr 0) tint)
                                                   (tptr tvoid)) tint)
                                    (Ssequence
                                      (Scall (Some _t'14)
                                        (Evar _same_peer (Tfunction
                                                           ((tptr (Tstruct _wg_peer noattr)) ::
                                                            (tptr (Tstruct _wg_peer noattr)) ::
                                                            nil) tint
                                                           cc_default))
                                        ((Eaddrof
                                           (Efield
                                             (Evar _p (Tstruct _pair noattr))
                                             _a_peer
                                             (Tstruct _wg_peer noattr))
                                           (tptr (Tstruct _wg_peer noattr))) ::
                                         (Eaddrof
                                           (Evar _before (Tstruct _wg_peer noattr))
                                           (tptr (Tstruct _wg_peer noattr))) ::
                                         nil))
                                      (Scall None
                                        (Evar _gp_assert (Tfunction
                                                           (tint :: nil)
                                                           tvoid cc_default))
                                        ((Ebinop One (Etempvar _t'14 tint)
                                           (Econst_int (Int.repr 0) tint)
                                           tint) :: nil)))
                                    Sskip)
                                  (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))
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
 Composite _pair Struct
   (Member_plain _a (Tstruct _wg_device noattr) ::
    Member_plain _b (Tstruct _wg_device noattr) ::
    Member_plain _a_indices (Tstruct _index_hashtable noattr) ::
    Member_plain _b_indices (Tstruct _index_hashtable noattr) ::
    Member_plain _a_keys (Tstruct _pubkey_hashtable noattr) ::
    Member_plain _b_keys (Tstruct _pubkey_hashtable noattr) ::
    Member_plain _a_peer (Tstruct _wg_peer noattr) ::
    Member_plain _b_peer (Tstruct _wg_peer noattr) :: nil)
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
 (_gp_assert,
   Gfun(External (EF_external "gp_assert"
                   (mksignature (AST.Xint :: nil) AST.Xvoid cc_default))
     (tint :: nil) tvoid cc_default)) ::
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
 (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_real_sec, Gvar v_wg_shim_real_sec) ::
 (_wg_shim_real_nsec, Gvar v_wg_shim_real_nsec) ::
 (_any_u64, Gfun(Internal f_any_u64)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_any_clocks, Gfun(Internal f_any_clocks)) ::
 (_new_device, Gfun(Internal f_new_device)) ::
 (_new_peer, Gfun(Internal f_new_peer)) ::
 (_new_pair, Gfun(Internal f_new_pair)) ::
 (_copy_peer, Gfun(Internal f_copy_peer)) ::
 (_same_peer, Gfun(Internal f_same_peer)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_shim_real_nsec :: _wg_shim_real_sec :: _wg_shim_boottime_ns ::
 _wg_noise_handshake_consume_response ::
 _wg_noise_handshake_create_response ::
 _wg_noise_handshake_consume_initiation ::
 _wg_noise_handshake_create_initiation ::
 _wg_noise_set_static_identity_private_key :: _wg_noise_handshake_init ::
 _wg_noise_init :: _gp_assert :: _nondet_bytes :: _nondet_u32 ::
 _nondet_u8 :: ___builtin_debug :: ___builtin_write32_reversed ::
 ___builtin_write16_reversed :: ___builtin_read32_reversed ::
 ___builtin_read16_reversed :: ___builtin_fnmsub :: ___builtin_fnmadd ::
 ___builtin_fmsub :: ___builtin_fmadd :: ___builtin_fmin ::
 ___builtin_fmax :: ___builtin_expect :: ___builtin_unreachable ::
 ___builtin_va_end :: ___builtin_va_copy :: ___builtin_va_arg ::
 ___builtin_va_start :: ___builtin_membar :: ___builtin_annot_intval ::
 ___builtin_annot :: ___builtin_sel :: ___builtin_memcpy_aligned ::
 ___builtin_sqrt :: ___builtin_fsqrt :: ___builtin_fabsf ::
 ___builtin_fabs :: ___builtin_ctzll :: ___builtin_ctzl :: ___builtin_ctz ::
 ___builtin_clzll :: ___builtin_clzl :: ___builtin_clz ::
 ___builtin_bswap16 :: ___builtin_bswap32 :: ___builtin_bswap ::
 ___builtin_bswap64 :: ___builtin_ais_annot :: ___compcert_i64_umulh ::
 ___compcert_i64_smulh :: ___compcert_i64_sar :: ___compcert_i64_shr ::
 ___compcert_i64_shl :: ___compcert_i64_umod :: ___compcert_i64_smod ::
 ___compcert_i64_udiv :: ___compcert_i64_sdiv :: ___compcert_i64_utof ::
 ___compcert_i64_stof :: ___compcert_i64_utod :: ___compcert_i64_stod ::
 ___compcert_i64_dtou :: ___compcert_i64_dtos :: ___compcert_va_composite ::
 ___compcert_va_float64 :: ___compcert_va_int64 :: ___compcert_va_int32 ::
 nil).

Definition prog : Clight.program := 
  mkprogram composites global_definitions public_idents _main Logic.I.


