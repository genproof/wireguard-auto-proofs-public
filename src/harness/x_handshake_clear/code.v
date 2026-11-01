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
  Definition source_file := "harness/x_handshake_clear.c".
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
Definition _alloc_failures : ident := $"alloc_failures".
Definition _allocs : ident := $"allocs".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _bt0 : ident := $"bt0".
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
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _counter : ident := $"counter".
Definition _current_keypair : ident := $"current_keypair".
Definition _d : ident := $"d".
Definition _dev : ident := $"dev".
Definition _dev_same : ident := $"dev_same".
Definition _dev_snap : ident := $"dev_snap".
Definition _dev_take : ident := $"dev_take".
Definition _device : ident := $"device".
Definition _draw_boottime : ident := $"draw_boottime".
Definition _draw_hs_state : ident := $"draw_hs_state".
Definition _draw_peer_refs : ident := $"draw_peer_refs".
Definition _draw_steps : ident := $"draw_steps".
Definition _draw_u64 : ident := $"draw_u64".
Definition _ds : ident := $"ds".
Definition _e : ident := $"e".
Definition _entry : ident := $"entry".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _fill : ident := $"fill".
Definition _frees : ident := $"frees".
Definition _h : ident := $"h".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _hashed0 : ident := $"hashed0".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _hi : ident := $"hi".
Definition _hnode : ident := $"hnode".
Definition _hnodes_add : ident := $"hnodes_add".
Definition _hnodes_free : ident := $"hnodes_free".
Definition _hnodes_pick : ident := $"hnodes_pick".
Definition _hnodes_snap : ident := $"hnodes_snap".
Definition _hs_randomize : ident := $"hs_randomize".
Definition _hs_same_but_next : ident := $"hs_same_but_next".
Definition _hs_snap : ident := $"hs_snap".
Definition _hs_take : ident := $"hs_take".
Definition _hs_zeroed_from : ident := $"hs_zeroed_from".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _id : ident := $"id".
Definition _id0 : ident := $"id0".
Definition _index : ident := $"index".
Definition _index0 : ident := $"index0".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _initiator0 : ident := $"initiator0".
Definition _internal_id : ident := $"internal_id".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _it : ident := $"it".
Definition _itab : ident := $"itab".
Definition _j : ident := $"j".
Definition _k : ident := $"k".
Definition _kent : ident := $"kent".
Definition _kent_same_but_next : ident := $"kent_same_but_next".
Definition _kents_add : ident := $"kents_add".
Definition _kents_free : ident := $"kents_free".
Definition _kents_hashed : ident := $"kents_hashed".
Definition _kents_same_but_next : ident := $"kents_same_but_next".
Definition _kents_snap : ident := $"kents_snap".
Definition _kes : ident := $"kes".
Definition _key : ident := $"key".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kp : ident := $"kp".
Definition _kref : ident := $"kref".
Definition _l : ident := $"l".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _n : ident := $"n".
Definition _nd : ident := $"nd".
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
Definition _nondet_bytes : ident := $"nondet_bytes".
Definition _nondet_size : ident := $"nondet_size".
Definition _nondet_u32 : ident := $"nondet_u32".
Definition _nondet_u8 : ident := $"nondet_u8".
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
Definition _psk : ident := $"psk".
Definition _pt : ident := $"pt".
Definition _ptab : ident := $"ptab".
Definition _pub : ident := $"pub".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_malloc : ident := $"quickproof_malloc".
Definition _raw : ident := $"raw".
Definition _raw_priv : ident := $"raw_priv".
Definition _rbirth0 : ident := $"rbirth0".
Definition _rcnt0 : ident := $"rcnt0".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
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
Definition _rest : ident := $"rest".
Definition _rkey0 : ident := $"rkey0".
Definition _rvalid0 : ident := $"rvalid0".
Definition _rw_semaphore : ident := $"rw_semaphore".
Definition _s : ident := $"s".
Definition _sbirth0 : ident := $"sbirth0".
Definition _scnt0 : ident := $"scnt0".
Definition _secret : ident := $"secret".
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
Definition _skey0 : ident := $"skey0".
Definition _snap : ident := $"snap".
Definition _ss : ident := $"ss".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _svalid0 : ident := $"svalid0".
Definition _t : ident := $"t".
Definition _table_has : ident := $"table_has".
Definition _table_len : ident := $"table_len".
Definition _target : ident := $"target".
Definition _type : ident := $"type".
Definition _type0 : ident := $"type0".
Definition _unused : ident := $"unused".
Definition _v : ident := $"v".
Definition _w : ident := $"w".
Definition _wg : ident := $"wg".
Definition _wg_cookie_checker_init : ident := $"wg_cookie_checker_init".
Definition _wg_cookie_checker_precompute_device_keys : ident := $"wg_cookie_checker_precompute_device_keys".
Definition _wg_cookie_checker_precompute_peer_keys : ident := $"wg_cookie_checker_precompute_peer_keys".
Definition _wg_cookie_init : ident := $"wg_cookie_init".
Definition _wg_device : ident := $"wg_device".
Definition _wg_index_hashtable_insert : ident := $"wg_index_hashtable_insert".
Definition _wg_noise_handshake_clear : ident := $"wg_noise_handshake_clear".
Definition _wg_noise_handshake_init : ident := $"wg_noise_handshake_init".
Definition _wg_noise_set_static_identity_private_key : ident := $"wg_noise_set_static_identity_private_key".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_shim_alloc_failures : ident := $"wg_shim_alloc_failures".
Definition _wg_shim_allocs : ident := $"wg_shim_allocs".
Definition _wg_shim_boottime_ns : ident := $"wg_shim_boottime_ns".
Definition _wg_shim_frees : ident := $"wg_shim_frees".
Definition _wg_shim_peer_released : ident := $"wg_shim_peer_released".
Definition _wg_shim_refcount_warn : ident := $"wg_shim_refcount_warn".
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
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.
Definition _t'7 : ident := 134%positive.
Definition _t'8 : ident := 135%positive.
Definition _t'9 : ident := 136%positive.

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

Definition f_draw_hs_state := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u8 (Tfunction nil tuchar cc_default))
      nil)
    (Sswitch (Ebinop Omod (Etempvar _t'1 tuchar)
               (Econst_int (Int.repr 5) tint) tint)
      (LScons (Some 0)
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))
        (LScons (Some 1)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          (LScons (Some 2)
            (Sreturn (Some (Econst_int (Int.repr 2) tint)))
            (LScons (Some 3)
              (Sreturn (Some (Econst_int (Int.repr 3) tint)))
              (LScons None Sbreak LSnil)))))))
  (Sreturn (Some (Econst_int (Int.repr 4) tint))))
|}.

Definition f_hs_randomize := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_h, (tptr (Tstruct _noise_handshake noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tulong) :: (_t'2, tuint) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _draw_hs_state (Tfunction nil tint cc_default))
      nil)
    (Sassign
      (Efield
        (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
          (Tstruct _noise_handshake noattr)) _state tint)
      (Etempvar _t'1 tint)))
  (Ssequence
    (Scall None
      (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
      ((Efield
         (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
           (Tstruct _noise_handshake noattr)) _ephemeral_private
         (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
    (Ssequence
      (Scall None
        (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                              cc_default))
        ((Efield
           (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
             (Tstruct _noise_handshake noattr)) _remote_ephemeral
           (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Efield
             (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
               (Tstruct _noise_handshake noattr)) _hash (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                  tvoid cc_default))
            ((Efield
               (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                 (Tstruct _noise_handshake noattr)) _chaining_key
               (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) :: nil))
          (Ssequence
            (Scall None
              (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                    tvoid cc_default))
              ((Efield
                 (Ederef
                   (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                   (Tstruct _noise_handshake noattr)) _latest_timestamp
                 (tarray tuchar 12)) :: (Econst_int (Int.repr 12) tint) ::
               nil))
            (Ssequence
              (Ssequence
                (Scall (Some _t'2)
                  (Evar _nondet_u32 (Tfunction nil tuint cc_default)) nil)
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr)) _remote_index tuint)
                  (Etempvar _t'2 tuint)))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _draw_boottime (Tfunction nil tulong cc_default))
                  nil)
                (Sassign
                  (Efield
                    (Ederef
                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                      (Tstruct _noise_handshake noattr))
                    _last_initiation_consumption tulong)
                  (Etempvar _t'3 tulong))))))))))
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

Definition f_kents_same_but_next := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) ::
                (_t, (tptr (Tstruct _index_hashtable noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'3, tint) :: (_t'2, tint) :: (_t'1, tint) ::
               (_t'4, tbool) :: nil);
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
              (Sset _t'4
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                    (Tstruct _kent noattr)) _hashed0 tbool))
              (Sifthenelse (Etempvar _t'4 tbool)
                (Ssequence
                  (Ssequence
                    (Scall (Some _t'3)
                      (Evar _table_has (Tfunction
                                         ((tptr (Tstruct _index_hashtable noattr)) ::
                                          (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                          nil) tint cc_default))
                      ((Etempvar _t (tptr (Tstruct _index_hashtable noattr))) ::
                       (Eaddrof
                         (Efield
                           (Efield
                             (Ederef
                               (Etempvar _l (tptr (Tstruct _kent noattr)))
                               (Tstruct _kent noattr)) _kp
                             (Tstruct _noise_keypair noattr)) _entry
                           (Tstruct _index_hashtable_entry noattr))
                         (tptr (Tstruct _index_hashtable_entry noattr))) ::
                       nil))
                    (Sset _t'2
                      (Ecast (Eunop Onotbool (Etempvar _t'3 tint) tint)
                        tbool)))
                  (Sset _t'2 (Ecast (Etempvar _t'2 tint) tbool)))
                (Sset _t'2 (Ecast (Econst_int (Int.repr 0) tint) tbool))))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 0) tint)))
          Sskip)))
    (Sset _l
      (Efield
        (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
          (Tstruct _kent noattr)) _next (tptr (Tstruct _kent noattr)))))
  (Sreturn (Some (Econst_int (Int.repr 1) tint))))
|}.

Definition f_kents_hashed := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_l, (tptr (Tstruct _kent noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_n, tulong) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _n (Ecast (Econst_int (Int.repr 0) tint) tulong))
  (Ssequence
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _l (tptr (Tstruct _kent noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Efield
              (Efield
                (Efield
                  (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
                    (Tstruct _kent noattr)) _kp
                  (Tstruct _noise_keypair noattr)) _entry
                (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
          (Sifthenelse (Etempvar _t'1 tbool)
            (Sset _n
              (Ebinop Oadd (Etempvar _n tulong)
                (Econst_int (Int.repr 1) tint) tulong))
            Sskip)))
      (Sset _l
        (Efield
          (Ederef (Etempvar _l (tptr (Tstruct _kent noattr)))
            (Tstruct _kent noattr)) _next (tptr (Tstruct _kent noattr)))))
    (Sreturn (Some (Etempvar _n tulong)))))
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

Definition f_hs_same_but_next := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := ((_s, (tptr (Tstruct _hs_snap noattr))) ::
                (_h, (tptr (Tstruct _noise_handshake noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'23, tint) :: (_t'22, tint) :: (_t'21, tint) ::
               (_t'20, tint) :: (_t'19, tint) :: (_t'18, tint) ::
               (_t'17, tint) :: (_t'16, tint) :: (_t'15, tint) ::
               (_t'14, tint) :: (_t'13, tint) :: (_t'12, tint) ::
               (_t'11, tint) :: (_t'10, tint) :: (_t'9, tint) ::
               (_t'8, tint) :: (_t'7, tint) :: (_t'6, tint) ::
               (_t'5, tint) :: (_t'4, tint) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tint) :: (_t'39, tbool) ::
               (_t'38, tbool) :: (_t'37, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'36, (tptr (Tstruct _wg_peer noattr))) :: (_t'35, tint) ::
               (_t'34, tint) :: (_t'33, tuint) :: (_t'32, tuint) ::
               (_t'31, tint) :: (_t'30, tint) :: (_t'29, tulong) ::
               (_t'28, tulong) ::
               (_t'27, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'26, (tptr (Tstruct _noise_static_identity noattr))) ::
               (_t'25, tuint) :: (_t'24, tuint) :: nil);
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
                                (Sset _t'36
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                      (Tstruct _hs_snap noattr)) _peer
                                    (tptr (Tstruct _wg_peer noattr))))
                                (Ssequence
                                  (Sset _t'37
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _entry
                                        (Tstruct _index_hashtable_entry noattr))
                                      _peer (tptr (Tstruct _wg_peer noattr))))
                                  (Sifthenelse (Ebinop Oeq
                                                 (Etempvar _t'36 (tptr (Tstruct _wg_peer noattr)))
                                                 (Etempvar _t'37 (tptr (Tstruct _wg_peer noattr)))
                                                 tint)
                                    (Ssequence
                                      (Sset _t'38
                                        (Efield
                                          (Ederef
                                            (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                            (Tstruct _hs_snap noattr))
                                          _hashed tbool))
                                      (Ssequence
                                        (Sset _t'39
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                (Tstruct _noise_handshake noattr))
                                              _entry
                                              (Tstruct _index_hashtable_entry noattr))
                                            _hashed tbool))
                                        (Sset _t'1
                                          (Ecast
                                            (Ebinop Oeq
                                              (Etempvar _t'38 tbool)
                                              (Etempvar _t'39 tbool) tint)
                                            tbool))))
                                    (Sset _t'1
                                      (Econst_int (Int.repr 0) tint)))))
                              (Sifthenelse (Etempvar _t'1 tint)
                                (Ssequence
                                  (Sset _t'34
                                    (Efield
                                      (Ederef
                                        (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                        (Tstruct _hs_snap noattr)) _type
                                      tint))
                                  (Ssequence
                                    (Sset _t'35
                                      (Efield
                                        (Efield
                                          (Ederef
                                            (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                            (Tstruct _noise_handshake noattr))
                                          _entry
                                          (Tstruct _index_hashtable_entry noattr))
                                        _type tint))
                                    (Sset _t'2
                                      (Ecast
                                        (Ebinop Oeq (Etempvar _t'34 tint)
                                          (Etempvar _t'35 tint) tint) tbool))))
                                (Sset _t'2 (Econst_int (Int.repr 0) tint))))
                            (Sifthenelse (Etempvar _t'2 tint)
                              (Ssequence
                                (Sset _t'32
                                  (Efield
                                    (Ederef
                                      (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                      (Tstruct _hs_snap noattr)) _index
                                    tuint))
                                (Ssequence
                                  (Sset _t'33
                                    (Efield
                                      (Efield
                                        (Ederef
                                          (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                          (Tstruct _noise_handshake noattr))
                                        _entry
                                        (Tstruct _index_hashtable_entry noattr))
                                      _index tuint))
                                  (Sset _t'3
                                    (Ecast
                                      (Ebinop Oeq (Etempvar _t'32 tuint)
                                        (Etempvar _t'33 tuint) tint) tbool))))
                              (Sset _t'3 (Econst_int (Int.repr 0) tint))))
                          (Sifthenelse (Etempvar _t'3 tint)
                            (Ssequence
                              (Sset _t'30
                                (Efield
                                  (Ederef
                                    (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                    (Tstruct _hs_snap noattr)) _state tint))
                              (Ssequence
                                (Sset _t'31
                                  (Efield
                                    (Ederef
                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                      (Tstruct _noise_handshake noattr))
                                    _state tint))
                                (Sset _t'4
                                  (Ecast
                                    (Ebinop Oeq (Etempvar _t'30 tint)
                                      (Etempvar _t'31 tint) tint) tbool))))
                            (Sset _t'4 (Econst_int (Int.repr 0) tint))))
                        (Sifthenelse (Etempvar _t'4 tint)
                          (Ssequence
                            (Sset _t'28
                              (Efield
                                (Ederef
                                  (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                  (Tstruct _hs_snap noattr))
                                _last_initiation_consumption tulong))
                            (Ssequence
                              (Sset _t'29
                                (Efield
                                  (Ederef
                                    (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                    (Tstruct _noise_handshake noattr))
                                  _last_initiation_consumption tulong))
                              (Sset _t'5
                                (Ecast
                                  (Ebinop Oeq (Etempvar _t'28 tulong)
                                    (Etempvar _t'29 tulong) tint) tbool))))
                          (Sset _t'5 (Econst_int (Int.repr 0) tint))))
                      (Sifthenelse (Etempvar _t'5 tint)
                        (Ssequence
                          (Sset _t'26
                            (Efield
                              (Ederef
                                (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
                                (Tstruct _hs_snap noattr)) _static_identity
                              (tptr (Tstruct _noise_static_identity noattr))))
                          (Ssequence
                            (Sset _t'27
                              (Efield
                                (Ederef
                                  (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                  (Tstruct _noise_handshake noattr))
                                _static_identity
                                (tptr (Tstruct _noise_static_identity noattr))))
                            (Sset _t'6
                              (Ecast
                                (Ebinop Oeq
                                  (Etempvar _t'26 (tptr (Tstruct _noise_static_identity noattr)))
                                  (Etempvar _t'27 (tptr (Tstruct _noise_static_identity noattr)))
                                  tint) tbool))))
                        (Sset _t'6 (Econst_int (Int.repr 0) tint))))
                    (Sifthenelse (Etempvar _t'6 tint)
                      (Ssequence
                        (Scall (Some _t'8)
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
                        (Sset _t'7 (Ecast (Etempvar _t'8 tint) tbool)))
                      (Sset _t'7 (Econst_int (Int.repr 0) tint))))
                  (Sifthenelse (Etempvar _t'7 tint)
                    (Ssequence
                      (Scall (Some _t'10)
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
                      (Sset _t'9 (Ecast (Etempvar _t'10 tint) tbool)))
                    (Sset _t'9 (Econst_int (Int.repr 0) tint))))
                (Sifthenelse (Etempvar _t'9 tint)
                  (Ssequence
                    (Scall (Some _t'12)
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
                    (Sset _t'11 (Ecast (Etempvar _t'12 tint) tbool)))
                  (Sset _t'11 (Econst_int (Int.repr 0) tint))))
              (Sifthenelse (Etempvar _t'11 tint)
                (Ssequence
                  (Scall (Some _t'14)
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
                  (Sset _t'13 (Ecast (Etempvar _t'14 tint) tbool)))
                (Sset _t'13 (Econst_int (Int.repr 0) tint))))
            (Sifthenelse (Etempvar _t'13 tint)
              (Ssequence
                (Scall (Some _t'16)
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
                (Sset _t'15 (Ecast (Etempvar _t'16 tint) tbool)))
              (Sset _t'15 (Econst_int (Int.repr 0) tint))))
          (Sifthenelse (Etempvar _t'15 tint)
            (Ssequence
              (Scall (Some _t'18)
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
              (Sset _t'17 (Ecast (Etempvar _t'18 tint) tbool)))
            (Sset _t'17 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'17 tint)
          (Ssequence
            (Scall (Some _t'20)
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
            (Sset _t'19 (Ecast (Etempvar _t'20 tint) tbool)))
          (Sset _t'19 (Econst_int (Int.repr 0) tint))))
      (Sifthenelse (Etempvar _t'19 tint)
        (Ssequence
          (Scall (Some _t'22)
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
          (Sset _t'21 (Ecast (Etempvar _t'22 tint) tbool)))
        (Sset _t'21 (Econst_int (Int.repr 0) tint))))
    (Sifthenelse (Etempvar _t'21 tint)
      (Ssequence
        (Sset _t'24
          (Efield
            (Ederef (Etempvar _s (tptr (Tstruct _hs_snap noattr)))
              (Tstruct _hs_snap noattr)) _remote_index tuint))
        (Ssequence
          (Sset _t'25
            (Efield
              (Ederef (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                (Tstruct _noise_handshake noattr)) _remote_index tuint))
          (Sset _t'23
            (Ecast
              (Ebinop Oeq (Etempvar _t'24 tuint) (Etempvar _t'25 tuint) tint)
              tbool))))
      (Sset _t'23 (Econst_int (Int.repr 0) tint))))
  (Sreturn (Some (Etempvar _t'23 tint))))
|}.

Definition f_main := {|
  fn_return := tint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := ((_w, (Tstruct _wg_device noattr)) ::
              (_it, (Tstruct _index_hashtable noattr)) ::
              (_pt, (Tstruct _pubkey_hashtable noattr)) ::
              (_raw, (tarray tuchar 32)) :: (_pub, (tarray tuchar 32)) ::
              (_peers, (tptr (Tstruct _hnode noattr))) ::
              (_ds, (Tstruct _dev_snap noattr)) ::
              (_ss, (Tstruct _shim_snap noattr)) :: nil);
  fn_temps := ((_nd, (tptr (Tstruct _hnode noattr))) ::
               (_target, (tptr (Tstruct _hnode noattr))) ::
               (_kes, (tptr (Tstruct _kent noattr))) ::
               (_h, (tptr (Tstruct _noise_handshake noattr))) ::
               (_n, tulong) :: (_i, tulong) :: (_hashed, tulong) ::
               (_t'21, tint) :: (_t'20, tint) :: (_t'19, tint) ::
               (_t'18, tulong) :: (_t'17, tulong) :: (_t'16, tint) ::
               (_t'15, tint) :: (_t'14, tint) :: (_t'13, tint) ::
               (_t'12, tint) :: (_t'11, tint) :: (_t'10, tint) ::
               (_t'9, tint) :: (_t'8, tint) :: (_t'7, tint) ::
               (_t'6, tint) :: (_t'5, (tptr (Tstruct _hnode noattr))) ::
               (_t'4, (tptr (Tstruct _kent noattr))) :: (_t'3, tuchar) ::
               (_t'2, tulong) :: (_t'1, tulong) ::
               (_t'48, (tptr (Tstruct _hnode noattr))) ::
               (_t'47, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'46, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'45, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'44, (tptr (Tstruct _hnode noattr))) ::
               (_t'43, (tptr (Tstruct _hnode noattr))) ::
               (_t'42, (tptr (Tstruct _hnode noattr))) ::
               (_t'41, (tptr (Tstruct _wg_peer noattr))) :: (_t'40, tbool) ::
               (_t'39, tuint) :: (_t'38, tuint) ::
               (_t'37, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'36, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'35, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'34, tbool) :: (_t'33, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'32, tuint) :: (_t'31, tuint) ::
               (_t'30, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'29, (tptr (Tstruct _wg_peer noattr))) :: (_t'28, tuint) ::
               (_t'27, tuint) :: (_t'26, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'25, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'24, (tptr (Tstruct _wg_peer noattr))) :: (_t'23, tbool) ::
               (_t'22, (tptr (Tstruct _hnode noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sassign (Evar _peers (tptr (Tstruct _hnode noattr)))
      (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence
      (Ssequence
        (Scall (Some _t'1)
          (Evar _draw_boottime (Tfunction nil tulong cc_default)) nil)
        (Sassign (Evar _wg_shim_boottime_ns tulong) (Etempvar _t'1 tulong)))
      (Ssequence
        (Scall None
          (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil)
                                tvoid cc_default))
          ((Evar _raw (tarray tuchar 32)) ::
           (Econst_int (Int.repr 32) tint) :: nil))
        (Ssequence
          (Scall None
            (Evar _setup_device (Tfunction
                                  ((tptr (Tstruct _wg_device noattr)) ::
                                   (tptr (Tstruct _index_hashtable noattr)) ::
                                   (tptr (Tstruct _pubkey_hashtable noattr)) ::
                                   (tptr tuchar) :: nil) tvoid cc_default))
            ((Eaddrof (Evar _w (Tstruct _wg_device noattr))
               (tptr (Tstruct _wg_device noattr))) ::
             (Eaddrof (Evar _it (Tstruct _index_hashtable noattr))
               (tptr (Tstruct _index_hashtable noattr))) ::
             (Eaddrof (Evar _pt (Tstruct _pubkey_hashtable noattr))
               (tptr (Tstruct _pubkey_hashtable noattr))) ::
             (Evar _raw (tarray tuchar 32)) :: nil))
          (Ssequence
            (Ssequence
              (Scall (Some _t'2)
                (Evar _draw_steps (Tfunction nil tulong cc_default)) nil)
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
                      (Scall None
                        (Evar _nondet_bytes (Tfunction
                                              ((tptr tuchar) :: tulong ::
                                               nil) tvoid cc_default))
                        ((Evar _pub (tarray tuchar 32)) ::
                         (Econst_int (Int.repr 32) tint) :: nil))
                      (Scall None
                        (Evar _hnodes_add (Tfunction
                                            ((tptr (tptr (Tstruct _hnode noattr))) ::
                                             (tptr (Tstruct _wg_device noattr)) ::
                                             (tptr tuchar) :: tulong :: nil)
                                            (tptr (Tstruct _hnode noattr))
                                            cc_default))
                        ((Eaddrof
                           (Evar _peers (tptr (Tstruct _hnode noattr)))
                           (tptr (tptr (Tstruct _hnode noattr)))) ::
                         (Eaddrof (Evar _w (Tstruct _wg_device noattr))
                           (tptr (Tstruct _wg_device noattr))) ::
                         (Evar _pub (tarray tuchar 32)) ::
                         (Etempvar _i tulong) :: nil))))
                  (Sset _i
                    (Ebinop Oadd (Etempvar _i tulong)
                      (Econst_int (Int.repr 1) tint) tulong))))
              (Ssequence
                (Ssequence
                  (Sset _t'48 (Evar _peers (tptr (Tstruct _hnode noattr))))
                  (Sifthenelse (Ebinop Oeq
                                 (Etempvar _t'48 (tptr (Tstruct _hnode noattr)))
                                 (Ecast (Econst_int (Int.repr 0) tint)
                                   (tptr tvoid)) tint)
                    (Sreturn (Some (Econst_int (Int.repr 0) tint)))
                    Sskip))
                (Ssequence
                  (Ssequence
                    (Sset _nd (Evar _peers (tptr (Tstruct _hnode noattr))))
                    (Sloop
                      (Ssequence
                        (Sifthenelse (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                          Sskip
                          Sbreak)
                        (Ssequence
                          (Ssequence
                            (Sset _t'47
                              (Efield
                                (Ederef
                                  (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                  (Tstruct _hnode noattr)) _p
                                (tptr (Tstruct _wg_peer noattr))))
                            (Scall None
                              (Evar _hs_randomize (Tfunction
                                                    ((tptr (Tstruct _noise_handshake noattr)) ::
                                                     nil) tvoid cc_default))
                              ((Eaddrof
                                 (Efield
                                   (Ederef
                                     (Etempvar _t'47 (tptr (Tstruct _wg_peer noattr)))
                                     (Tstruct _wg_peer noattr)) _handshake
                                   (Tstruct _noise_handshake noattr))
                                 (tptr (Tstruct _noise_handshake noattr))) ::
                               nil)))
                          (Ssequence
                            (Ssequence
                              (Sset _t'46
                                (Efield
                                  (Ederef
                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                    (Tstruct _hnode noattr)) _p
                                  (tptr (Tstruct _wg_peer noattr))))
                              (Scall None
                                (Evar _peer_randomize_rest (Tfunction
                                                             ((tptr (Tstruct _wg_peer noattr)) ::
                                                              nil) tvoid
                                                             cc_default))
                                ((Etempvar _t'46 (tptr (Tstruct _wg_peer noattr))) ::
                                 nil)))
                            (Ssequence
                              (Scall (Some _t'3)
                                (Evar _nondet_u8 (Tfunction nil tuchar
                                                   cc_default)) nil)
                              (Sifthenelse (Ebinop One
                                             (Ebinop Omod
                                               (Etempvar _t'3 tuchar)
                                               (Econst_int (Int.repr 4) tint)
                                               tint)
                                             (Econst_int (Int.repr 0) tint)
                                             tint)
                                (Ssequence
                                  (Sset _t'45
                                    (Efield
                                      (Ederef
                                        (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                        (Tstruct _hnode noattr)) _p
                                      (tptr (Tstruct _wg_peer noattr))))
                                  (Scall None
                                    (Evar _wg_index_hashtable_insert 
                                    (Tfunction
                                      ((tptr (Tstruct _index_hashtable noattr)) ::
                                       (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                       nil) tuint cc_default))
                                    ((Eaddrof
                                       (Evar _it (Tstruct _index_hashtable noattr))
                                       (tptr (Tstruct _index_hashtable noattr))) ::
                                     (Eaddrof
                                       (Efield
                                         (Efield
                                           (Ederef
                                             (Etempvar _t'45 (tptr (Tstruct _wg_peer noattr)))
                                             (Tstruct _wg_peer noattr))
                                           _handshake
                                           (Tstruct _noise_handshake noattr))
                                         _entry
                                         (Tstruct _index_hashtable_entry noattr))
                                       (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                     nil)))
                                Sskip)))))
                      (Sset _nd
                        (Efield
                          (Ederef
                            (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                            (Tstruct _hnode noattr)) _next
                          (tptr (Tstruct _hnode noattr))))))
                  (Ssequence
                    (Ssequence
                      (Ssequence
                        (Sset _t'44
                          (Evar _peers (tptr (Tstruct _hnode noattr))))
                        (Scall (Some _t'4)
                          (Evar _kents_add (Tfunction
                                             ((tptr (Tstruct _index_hashtable noattr)) ::
                                              (tptr (Tstruct _hnode noattr)) ::
                                              (tptr (Tstruct _wg_peer noattr)) ::
                                              tint :: nil)
                                             (tptr (Tstruct _kent noattr))
                                             cc_default))
                          ((Eaddrof
                             (Evar _it (Tstruct _index_hashtable noattr))
                             (tptr (Tstruct _index_hashtable noattr))) ::
                           (Etempvar _t'44 (tptr (Tstruct _hnode noattr))) ::
                           (Ecast (Econst_int (Int.repr 0) tint)
                             (tptr tvoid)) ::
                           (Econst_int (Int.repr 1) tint) :: nil)))
                      (Sset _kes
                        (Etempvar _t'4 (tptr (Tstruct _kent noattr)))))
                    (Ssequence
                      (Ssequence
                        (Ssequence
                          (Sset _t'43
                            (Evar _peers (tptr (Tstruct _hnode noattr))))
                          (Scall (Some _t'5)
                            (Evar _hnodes_pick (Tfunction
                                                 ((tptr (Tstruct _hnode noattr)) ::
                                                  nil)
                                                 (tptr (Tstruct _hnode noattr))
                                                 cc_default))
                            ((Etempvar _t'43 (tptr (Tstruct _hnode noattr))) ::
                             nil)))
                        (Sset _target
                          (Etempvar _t'5 (tptr (Tstruct _hnode noattr)))))
                      (Ssequence
                        (Ssequence
                          (Sset _t'42
                            (Evar _peers (tptr (Tstruct _hnode noattr))))
                          (Scall None
                            (Evar _hnodes_snap (Tfunction
                                                 ((tptr (Tstruct _hnode noattr)) ::
                                                  nil) tvoid cc_default))
                            ((Etempvar _t'42 (tptr (Tstruct _hnode noattr))) ::
                             nil)))
                        (Ssequence
                          (Scall None
                            (Evar _kents_snap (Tfunction
                                                ((tptr (Tstruct _kent noattr)) ::
                                                 nil) tvoid cc_default))
                            ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                             nil))
                          (Ssequence
                            (Scall None
                              (Evar _dev_take (Tfunction
                                                ((tptr (Tstruct _dev_snap noattr)) ::
                                                 (tptr (Tstruct _wg_device noattr)) ::
                                                 nil) tvoid cc_default))
                              ((Eaddrof (Evar _ds (Tstruct _dev_snap noattr))
                                 (tptr (Tstruct _dev_snap noattr))) ::
                               (Eaddrof (Evar _w (Tstruct _wg_device noattr))
                                 (tptr (Tstruct _wg_device noattr))) :: nil))
                            (Ssequence
                              (Scall None
                                (Evar _shim_take (Tfunction
                                                   ((tptr (Tstruct _shim_snap noattr)) ::
                                                    nil) tvoid cc_default))
                                ((Eaddrof
                                   (Evar _ss (Tstruct _shim_snap noattr))
                                   (tptr (Tstruct _shim_snap noattr))) ::
                                 nil))
                              (Ssequence
                                (Ssequence
                                  (Sset _t'41
                                    (Efield
                                      (Ederef
                                        (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                        (Tstruct _hnode noattr)) _p
                                      (tptr (Tstruct _wg_peer noattr))))
                                  (Sset _h
                                    (Eaddrof
                                      (Efield
                                        (Ederef
                                          (Etempvar _t'41 (tptr (Tstruct _wg_peer noattr)))
                                          (Tstruct _wg_peer noattr))
                                        _handshake
                                        (Tstruct _noise_handshake noattr))
                                      (tptr (Tstruct _noise_handshake noattr)))))
                                (Ssequence
                                  (Scall None
                                    (Evar _wg_noise_handshake_clear (Tfunction
                                                                    ((tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil)
                                                                    tvoid
                                                                    cc_default))
                                    ((Etempvar _h (tptr (Tstruct _noise_handshake noattr))) ::
                                     nil))
                                  (Ssequence
                                    (Sloop
                                      (Ssequence
                                        (Ssequence
                                          (Ssequence
                                            (Scall (Some _t'6)
                                              (Evar _hs_zeroed_from (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                              ((Eaddrof
                                                 (Efield
                                                   (Ederef
                                                     (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                     (Tstruct _hnode noattr))
                                                   _snap
                                                   (Tstruct _hs_snap noattr))
                                                 (tptr (Tstruct _hs_snap noattr))) ::
                                               (Etempvar _h (tptr (Tstruct _noise_handshake noattr))) ::
                                               nil))
                                            (Sifthenelse (Etempvar _t'6 tint)
                                              (Ssequence
                                                (Sset _t'40
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                        (Tstruct _noise_handshake noattr))
                                                      _entry
                                                      (Tstruct _index_hashtable_entry noattr))
                                                    _hashed tbool))
                                                (Sset _t'7
                                                  (Ecast
                                                    (Eunop Onotbool
                                                      (Etempvar _t'40 tbool)
                                                      tint) tbool)))
                                              (Sset _t'7
                                                (Econst_int (Int.repr 0) tint))))
                                          (Sifthenelse (Etempvar _t'7 tint)
                                            (Ssequence
                                              (Sset _t'38
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _index tuint))
                                              (Ssequence
                                                (Sset _t'39
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                        (Tstruct _hnode noattr))
                                                      _snap
                                                      (Tstruct _hs_snap noattr))
                                                    _index tuint))
                                                (Sset _t'8
                                                  (Ecast
                                                    (Ebinop Oeq
                                                      (Etempvar _t'38 tuint)
                                                      (Etempvar _t'39 tuint)
                                                      tint) tbool))))
                                            (Sset _t'8
                                              (Econst_int (Int.repr 0) tint))))
                                        (Sifthenelse (Eunop Onotbool
                                                       (Etempvar _t'8 tint)
                                                       tint)
                                          (Scall None
                                            (Evar _check_failed (Tfunction
                                                                  nil tvoid
                                                                  cc_default))
                                            nil)
                                          Sskip))
                                      Sbreak)
                                    (Ssequence
                                      (Ssequence
                                        (Sset _t'34
                                          (Efield
                                            (Efield
                                              (Ederef
                                                (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                (Tstruct _hnode noattr))
                                              _snap
                                              (Tstruct _hs_snap noattr))
                                            _hashed tbool))
                                        (Sifthenelse (Etempvar _t'34 tbool)
                                          (Sloop
                                            (Ssequence
                                              (Sset _t'37
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _next
                                                  (tptr (Tstruct _index_hashtable_entry noattr))))
                                              (Sifthenelse (Eunop Onotbool
                                                             (Ebinop Oeq
                                                               (Etempvar _t'37 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                               (Ecast
                                                                 (Econst_int (Int.repr 0) tint)
                                                                 (tptr tvoid))
                                                               tint) tint)
                                                (Scall None
                                                  (Evar _check_failed 
                                                  (Tfunction nil tvoid
                                                    cc_default)) nil)
                                                Sskip))
                                            Sbreak)
                                          (Sloop
                                            (Ssequence
                                              (Sset _t'35
                                                (Efield
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _h (tptr (Tstruct _noise_handshake noattr)))
                                                      (Tstruct _noise_handshake noattr))
                                                    _entry
                                                    (Tstruct _index_hashtable_entry noattr))
                                                  _next
                                                  (tptr (Tstruct _index_hashtable_entry noattr))))
                                              (Ssequence
                                                (Sset _t'36
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                        (Tstruct _hnode noattr))
                                                      _snap
                                                      (Tstruct _hs_snap noattr))
                                                    _next
                                                    (tptr (Tstruct _index_hashtable_entry noattr))))
                                                (Sifthenelse (Eunop Onotbool
                                                               (Ebinop Oeq
                                                                 (Etempvar _t'35 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                 (Etempvar _t'36 (tptr (Tstruct _index_hashtable_entry noattr)))
                                                                 tint) tint)
                                                  (Scall None
                                                    (Evar _check_failed 
                                                    (Tfunction nil tvoid
                                                      cc_default)) nil)
                                                  Sskip)))
                                            Sbreak)))
                                      (Ssequence
                                        (Sloop
                                          (Ssequence
                                            (Ssequence
                                              (Sset _t'30
                                                (Efield
                                                  (Ederef
                                                    (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                    (Tstruct _hnode noattr))
                                                  _p
                                                  (tptr (Tstruct _wg_peer noattr))))
                                              (Ssequence
                                                (Sset _t'31
                                                  (Efield
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _t'30 (tptr (Tstruct _wg_peer noattr)))
                                                        (Tstruct _wg_peer noattr))
                                                      _refcount
                                                      (Tstruct _kref noattr))
                                                    _refcount tuint))
                                                (Ssequence
                                                  (Sset _t'32
                                                    (Efield
                                                      (Ederef
                                                        (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                        (Tstruct _hnode noattr))
                                                      _refs tuint))
                                                  (Sifthenelse (Ebinop Oeq
                                                                 (Etempvar _t'31 tuint)
                                                                 (Etempvar _t'32 tuint)
                                                                 tint)
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'33
                                                          (Efield
                                                            (Ederef
                                                              (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                              (Tstruct _hnode noattr))
                                                            _p
                                                            (tptr (Tstruct _wg_peer noattr))))
                                                        (Scall (Some _t'10)
                                                          (Evar _pr_same 
                                                          (Tfunction
                                                            ((tptr (Tstruct _pr_snap noattr)) ::
                                                             (tptr (Tstruct _wg_peer noattr)) ::
                                                             nil) tint
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Efield
                                                               (Ederef
                                                                 (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                                 (Tstruct _hnode noattr))
                                                               _rest
                                                               (Tstruct _pr_snap noattr))
                                                             (tptr (Tstruct _pr_snap noattr))) ::
                                                           (Etempvar _t'33 (tptr (Tstruct _wg_peer noattr))) ::
                                                           nil)))
                                                      (Sset _t'9
                                                        (Ecast
                                                          (Etempvar _t'10 tint)
                                                          tbool)))
                                                    (Sset _t'9
                                                      (Econst_int (Int.repr 0) tint))))))
                                            (Sifthenelse (Eunop Onotbool
                                                           (Etempvar _t'9 tint)
                                                           tint)
                                              (Scall None
                                                (Evar _check_failed (Tfunction
                                                                    nil tvoid
                                                                    cc_default))
                                                nil)
                                              Sskip))
                                          Sbreak)
                                        (Ssequence
                                          (Sset _hashed
                                            (Ecast
                                              (Econst_int (Int.repr 0) tint)
                                              tulong))
                                          (Ssequence
                                            (Ssequence
                                              (Sset _nd
                                                (Evar _peers (tptr (Tstruct _hnode noattr))))
                                              (Sloop
                                                (Ssequence
                                                  (Sifthenelse (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                    Sskip
                                                    Sbreak)
                                                  (Ssequence
                                                    (Sifthenelse (Ebinop Oeq
                                                                   (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                   (Etempvar _target (tptr (Tstruct _hnode noattr)))
                                                                   tint)
                                                      Scontinue
                                                      Sskip)
                                                    (Ssequence
                                                      (Sloop
                                                        (Ssequence
                                                          (Ssequence
                                                            (Ssequence
                                                              (Ssequence
                                                                (Sset _t'29
                                                                  (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                (Scall (Some _t'11)
                                                                  (Evar _hs_same_but_next 
                                                                  (Tfunction
                                                                    ((tptr (Tstruct _hs_snap noattr)) ::
                                                                    (tptr (Tstruct _noise_handshake noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                  ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _snap
                                                                    (Tstruct _hs_snap noattr))
                                                                    (tptr (Tstruct _hs_snap noattr))) ::
                                                                   (Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'29 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    (tptr (Tstruct _noise_handshake noattr))) ::
                                                                   nil)))
                                                              (Sifthenelse (Etempvar _t'11 tint)
                                                                (Ssequence
                                                                  (Sset _t'26
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                  (Ssequence
                                                                    (Sset _t'27
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'26 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _refcount
                                                                    (Tstruct _kref noattr))
                                                                    _refcount
                                                                    tuint))
                                                                    (Ssequence
                                                                    (Sset _t'28
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _refs
                                                                    tuint))
                                                                    (Sset _t'12
                                                                    (Ecast
                                                                    (Ebinop Oeq
                                                                    (Etempvar _t'27 tuint)
                                                                    (Etempvar _t'28 tuint)
                                                                    tint)
                                                                    tbool)))))
                                                                (Sset _t'12
                                                                  (Econst_int (Int.repr 0) tint))))
                                                            (Sifthenelse (Etempvar _t'12 tint)
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'25
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                  (Scall (Some _t'14)
                                                                    (Evar _pr_same 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _pr_snap noattr)) ::
                                                                    (tptr (Tstruct _wg_peer noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _rest
                                                                    (Tstruct _pr_snap noattr))
                                                                    (tptr (Tstruct _pr_snap noattr))) ::
                                                                    (Etempvar _t'25 (tptr (Tstruct _wg_peer noattr))) ::
                                                                    nil)))
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
                                                              (Tfunction nil
                                                                tvoid
                                                                cc_default))
                                                              nil)
                                                            Sskip))
                                                        Sbreak)
                                                      (Ssequence
                                                        (Sset _t'23
                                                          (Efield
                                                            (Efield
                                                              (Ederef
                                                                (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                (Tstruct _hnode noattr))
                                                              _snap
                                                              (Tstruct _hs_snap noattr))
                                                            _hashed tbool))
                                                        (Sifthenelse (Etempvar _t'23 tbool)
                                                          (Ssequence
                                                            (Sloop
                                                              (Ssequence
                                                                (Ssequence
                                                                  (Sset _t'24
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                                    (Tstruct _hnode noattr))
                                                                    _p
                                                                    (tptr (Tstruct _wg_peer noattr))))
                                                                  (Scall (Some _t'15)
                                                                    (Evar _table_has 
                                                                    (Tfunction
                                                                    ((tptr (Tstruct _index_hashtable noattr)) ::
                                                                    (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                                                    nil) tint
                                                                    cc_default))
                                                                    ((Eaddrof
                                                                    (Evar _it (Tstruct _index_hashtable noattr))
                                                                    (tptr (Tstruct _index_hashtable noattr))) ::
                                                                    (Eaddrof
                                                                    (Efield
                                                                    (Efield
                                                                    (Ederef
                                                                    (Etempvar _t'24 (tptr (Tstruct _wg_peer noattr)))
                                                                    (Tstruct _wg_peer noattr))
                                                                    _handshake
                                                                    (Tstruct _noise_handshake noattr))
                                                                    _entry
                                                                    (Tstruct _index_hashtable_entry noattr))
                                                                    (tptr (Tstruct _index_hashtable_entry noattr))) ::
                                                                    nil)))
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
                                                            (Sset _hashed
                                                              (Ebinop Oadd
                                                                (Etempvar _hashed tulong)
                                                                (Econst_int (Int.repr 1) tint)
                                                                tulong)))
                                                          Sskip)))))
                                                (Sset _nd
                                                  (Efield
                                                    (Ederef
                                                      (Etempvar _nd (tptr (Tstruct _hnode noattr)))
                                                      (Tstruct _hnode noattr))
                                                    _next
                                                    (tptr (Tstruct _hnode noattr))))))
                                            (Ssequence
                                              (Sloop
                                                (Ssequence
                                                  (Scall (Some _t'16)
                                                    (Evar _kents_same_but_next 
                                                    (Tfunction
                                                      ((tptr (Tstruct _kent noattr)) ::
                                                       (tptr (Tstruct _index_hashtable noattr)) ::
                                                       nil) tint cc_default))
                                                    ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                     (Eaddrof
                                                       (Evar _it (Tstruct _index_hashtable noattr))
                                                       (tptr (Tstruct _index_hashtable noattr))) ::
                                                     nil))
                                                  (Sifthenelse (Eunop Onotbool
                                                                 (Etempvar _t'16 tint)
                                                                 tint)
                                                    (Scall None
                                                      (Evar _check_failed 
                                                      (Tfunction nil tvoid
                                                        cc_default)) nil)
                                                    Sskip))
                                                Sbreak)
                                              (Ssequence
                                                (Sloop
                                                  (Ssequence
                                                    (Ssequence
                                                      (Scall (Some _t'17)
                                                        (Evar _table_len 
                                                        (Tfunction
                                                          ((tptr (Tstruct _index_hashtable noattr)) ::
                                                           nil) tulong
                                                          cc_default))
                                                        ((Eaddrof
                                                           (Evar _it (Tstruct _index_hashtable noattr))
                                                           (tptr (Tstruct _index_hashtable noattr))) ::
                                                         nil))
                                                      (Scall (Some _t'18)
                                                        (Evar _kents_hashed 
                                                        (Tfunction
                                                          ((tptr (Tstruct _kent noattr)) ::
                                                           nil) tulong
                                                          cc_default))
                                                        ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                         nil)))
                                                    (Sifthenelse (Eunop Onotbool
                                                                   (Ebinop Oeq
                                                                    (Etempvar _t'17 tulong)
                                                                    (Ebinop Oadd
                                                                    (Etempvar _hashed tulong)
                                                                    (Etempvar _t'18 tulong)
                                                                    tulong)
                                                                    tint)
                                                                   tint)
                                                      (Scall None
                                                        (Evar _check_failed 
                                                        (Tfunction nil tvoid
                                                          cc_default)) nil)
                                                      Sskip))
                                                  Sbreak)
                                                (Ssequence
                                                  (Sloop
                                                    (Ssequence
                                                      (Ssequence
                                                        (Scall (Some _t'19)
                                                          (Evar _dev_same 
                                                          (Tfunction
                                                            ((tptr (Tstruct _dev_snap noattr)) ::
                                                             (tptr (Tstruct _wg_device noattr)) ::
                                                             nil) tint
                                                            cc_default))
                                                          ((Eaddrof
                                                             (Evar _ds (Tstruct _dev_snap noattr))
                                                             (tptr (Tstruct _dev_snap noattr))) ::
                                                           (Eaddrof
                                                             (Evar _w (Tstruct _wg_device noattr))
                                                             (tptr (Tstruct _wg_device noattr))) ::
                                                           nil))
                                                        (Sifthenelse (Etempvar _t'19 tint)
                                                          (Ssequence
                                                            (Scall (Some _t'21)
                                                              (Evar _shim_same 
                                                              (Tfunction
                                                                ((tptr (Tstruct _shim_snap noattr)) ::
                                                                 nil) tint
                                                                cc_default))
                                                              ((Eaddrof
                                                                 (Evar _ss (Tstruct _shim_snap noattr))
                                                                 (tptr (Tstruct _shim_snap noattr))) ::
                                                               nil))
                                                            (Sset _t'20
                                                              (Ecast
                                                                (Etempvar _t'21 tint)
                                                                tbool)))
                                                          (Sset _t'20
                                                            (Econst_int (Int.repr 0) tint))))
                                                      (Sifthenelse (Eunop Onotbool
                                                                    (Etempvar _t'20 tint)
                                                                    tint)
                                                        (Scall None
                                                          (Evar _check_failed 
                                                          (Tfunction nil
                                                            tvoid cc_default))
                                                          nil)
                                                        Sskip))
                                                    Sbreak)
                                                  (Ssequence
                                                    (Scall None
                                                      (Evar _kents_free 
                                                      (Tfunction
                                                        ((tptr (Tstruct _kent noattr)) ::
                                                         nil) tvoid
                                                        cc_default))
                                                      ((Etempvar _kes (tptr (Tstruct _kent noattr))) ::
                                                       nil))
                                                    (Ssequence
                                                      (Ssequence
                                                        (Sset _t'22
                                                          (Evar _peers (tptr (Tstruct _hnode noattr))))
                                                        (Scall None
                                                          (Evar _hnodes_free 
                                                          (Tfunction
                                                            ((tptr (Tstruct _hnode noattr)) ::
                                                             nil) tvoid
                                                            cc_default))
                                                          ((Etempvar _t'22 (tptr (Tstruct _hnode noattr))) ::
                                                           nil)))
                                                      (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))))))))))))))))))))))))
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
 (_quickproof_malloc,
   Gfun(External (EF_external "quickproof_malloc"
                   (mksignature (AST.Xlong :: nil) AST.Xptr cc_default))
     (tulong :: nil) (tptr tvoid) cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_wg_index_hashtable_insert,
   Gfun(External (EF_external "wg_index_hashtable_insert"
                   (mksignature (AST.Xptr :: AST.Xptr :: nil) AST.Xint
                     cc_default))
     ((tptr (Tstruct _index_hashtable noattr)) ::
      (tptr (Tstruct _index_hashtable_entry noattr)) :: nil) tuint
     cc_default)) ::
 (_wg_shim_refcount_warn, Gvar v_wg_shim_refcount_warn) ::
 (_wg_noise_handshake_init,
   Gfun(External (EF_external "wg_noise_handshake_init"
                   (mksignature
                     (AST.Xptr :: AST.Xptr :: AST.Xptr :: AST.Xptr ::
                      AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _noise_handshake noattr)) ::
      (tptr (Tstruct _noise_static_identity noattr)) :: (tptr tuchar) ::
      (tptr tuchar) :: (tptr (Tstruct _wg_peer noattr)) :: nil) tvoid
     cc_default)) ::
 (_wg_noise_handshake_clear,
   Gfun(External (EF_external "wg_noise_handshake_clear"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr (Tstruct _noise_handshake noattr)) :: nil) tvoid cc_default)) ::
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
 (_check_failed, Gfun(Internal f_check_failed)) ::
 (_bytes_eq, Gfun(Internal f_bytes_eq)) ::
 (_bytes_zero, Gfun(Internal f_bytes_zero)) ::
 (_bytes_copy, Gfun(Internal f_bytes_copy)) ::
 (_bytes_set, Gfun(Internal f_bytes_set)) ::
 (_draw_steps, Gfun(Internal f_draw_steps)) ::
 (_draw_u64, Gfun(Internal f_draw_u64)) ::
 (_draw_boottime, Gfun(Internal f_draw_boottime)) ::
 (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_allocs, Gvar v_wg_shim_allocs) ::
 (_wg_shim_alloc_failures, Gvar v_wg_shim_alloc_failures) ::
 (_wg_shim_frees, Gvar v_wg_shim_frees) ::
 (_wg_shim_peer_released, Gvar v_wg_shim_peer_released) ::
 (_setup_device, Gfun(Internal f_setup_device)) ::
 (_setup_peer, Gfun(Internal f_setup_peer)) ::
 (_table_has, Gfun(Internal f_table_has)) ::
 (_table_len, Gfun(Internal f_table_len)) ::
 (_hs_take, Gfun(Internal f_hs_take)) ::
 (_hs_zeroed_from, Gfun(Internal f_hs_zeroed_from)) ::
 (_ck_take, Gfun(Internal f_ck_take)) ::
 (_ck_same, Gfun(Internal f_ck_same)) ::
 (_pr_take, Gfun(Internal f_pr_take)) ::
 (_pr_same_but_cookie, Gfun(Internal f_pr_same_but_cookie)) ::
 (_pr_same, Gfun(Internal f_pr_same)) ::
 (_draw_hs_state, Gfun(Internal f_draw_hs_state)) ::
 (_hs_randomize, Gfun(Internal f_hs_randomize)) ::
 (_draw_peer_refs, Gfun(Internal f_draw_peer_refs)) ::
 (_hnodes_snap, Gfun(Internal f_hnodes_snap)) ::
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
 (_kents_same_but_next, Gfun(Internal f_kents_same_but_next)) ::
 (_kents_hashed, Gfun(Internal f_kents_hashed)) ::
 (_kents_free, Gfun(Internal f_kents_free)) ::
 (_hs_same_but_next, Gfun(Internal f_hs_same_but_next)) ::
 (_main, Gfun(Internal f_main)) :: nil).

Definition public_idents : list ident :=
(_main :: _wg_shim_peer_released :: _wg_shim_frees ::
 _wg_shim_alloc_failures :: _wg_shim_allocs :: _wg_shim_boottime_ns ::
 _wg_cookie_init :: _wg_cookie_checker_precompute_peer_keys ::
 _wg_cookie_checker_precompute_device_keys :: _wg_cookie_checker_init ::
 _wg_noise_set_static_identity_private_key :: _wg_noise_handshake_clear ::
 _wg_noise_handshake_init :: _wg_shim_refcount_warn ::
 _wg_index_hashtable_insert :: _quickproof_free :: _quickproof_malloc ::
 _nondet_bytes :: _nondet_size :: _nondet_u32 :: _nondet_u8 ::
 ___builtin_debug :: ___builtin_write32_reversed ::
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


