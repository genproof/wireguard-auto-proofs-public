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
  Definition source_file := "patch/wg_shim.c".
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
Definition ___crypto_memneq : ident := $"__crypto_memneq".
Definition ___crypto_xor : ident := $"__crypto_xor".
Definition ___gp_atomic64_t : ident := $"__gp_atomic64_t".
Definition ___gp_spinlock_t : ident := $"__gp_spinlock_t".
Definition _a : ident := $"a".
Definition _b : ident := $"b".
Definition _backtrack : ident := $"backtrack".
Definition _birthdate : ident := $"birthdate".
Definition _birthday_nanoseconds : ident := $"birthday_nanoseconds".
Definition _buf : ident := $"buf".
Definition _calloc : ident := $"calloc".
Definition _chaining_key : ident := $"chaining_key".
Definition _cookie : ident := $"cookie".
Definition _cookie_checker : ident := $"cookie_checker".
Definition _cookie_decryption_key : ident := $"cookie_decryption_key".
Definition _cookie_encryption_key : ident := $"cookie_encryption_key".
Definition _counter : ident := $"counter".
Definition _current_keypair : ident := $"current_keypair".
Definition _data : ident := $"data".
Definition _dev : ident := $"dev".
Definition _device : ident := $"device".
Definition _dst : ident := $"dst".
Definition _e : ident := $"e".
Definition _entry : ident := $"entry".
Definition _ephemeral_private : ident := $"ephemeral_private".
Definition _expiration_seconds : ident := $"expiration_seconds".
Definition _flags : ident := $"flags".
Definition _get_random_bytes : ident := $"get_random_bytes".
Definition _get_random_bytes_wait : ident := $"get_random_bytes_wait".
Definition _get_random_u32 : ident := $"get_random_u32".
Definition _handshake : ident := $"handshake".
Definition _has_identity : ident := $"has_identity".
Definition _hash : ident := $"hash".
Definition _hashed : ident := $"hashed".
Definition _have_sent_mac1 : ident := $"have_sent_mac1".
Definition _head : ident := $"head".
Definition _i : ident := $"i".
Definition _i_am_the_initiator : ident := $"i_am_the_initiator".
Definition _in6_addr : ident := $"in6_addr".
Definition _in_addr : ident := $"in_addr".
Definition _index : ident := $"index".
Definition _index_hashtable : ident := $"index_hashtable".
Definition _index_hashtable_entry : ident := $"index_hashtable_entry".
Definition _internal_id : ident := $"internal_id".
Definition _ip4 : ident := $"ip4".
Definition _ip6 : ident := $"ip6".
Definition _iphdr : ident := $"iphdr".
Definition _ipv6hdr : ident := $"ipv6hdr".
Definition _is_dead : ident := $"is_dead".
Definition _is_valid : ident := $"is_valid".
Definition _iter_entry : ident := $"iter_entry".
Definition _iter_peer : ident := $"iter_peer".
Definition _key : ident := $"key".
Definition _keypair_update_lock : ident := $"keypair_update_lock".
Definition _keypairs : ident := $"keypairs".
Definition _kfree : ident := $"kfree".
Definition _kfree_sensitive : ident := $"kfree_sensitive".
Definition _kref : ident := $"kref".
Definition _ktime_get_coarse_boottime_ns : ident := $"ktime_get_coarse_boottime_ns".
Definition _ktime_get_real_ts64 : ident := $"ktime_get_real_ts64".
Definition _kzalloc : ident := $"kzalloc".
Definition _last_initiation_consumption : ident := $"last_initiation_consumption".
Definition _last_mac1_sent : ident := $"last_mac1_sent".
Definition _last_sent_handshake : ident := $"last_sent_handshake".
Definition _latest_cookie : ident := $"latest_cookie".
Definition _latest_timestamp : ident := $"latest_timestamp".
Definition _len : ident := $"len".
Definition _link : ident := $"link".
Definition _lock : ident := $"lock".
Definition _main : ident := $"main".
Definition _memcmp : ident := $"memcmp".
Definition _message_mac1_key : ident := $"message_mac1_key".
Definition _neq : ident := $"neq".
Definition _net : ident := $"net".
Definition _net__1 : ident := $"net__1".
Definition _net_device : ident := $"net_device".
Definition _new : ident := $"new".
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
Definition _old : ident := $"old".
Definition _p : ident := $"p".
Definition _peer : ident := $"peer".
Definition _peer_hashtable : ident := $"peer_hashtable".
Definition _precomputed_static_static : ident := $"precomputed_static_static".
Definition _preshared_key : ident := $"preshared_key".
Definition _previous_keypair : ident := $"previous_keypair".
Definition _protocol : ident := $"protocol".
Definition _pubkey : ident := $"pubkey".
Definition _pubkey_hashtable : ident := $"pubkey_hashtable".
Definition _pubkey_next : ident := $"pubkey_next".
Definition _quickproof_free : ident := $"quickproof_free".
Definition _quickproof_zero_page : ident := $"quickproof_zero_page".
Definition _r : ident := $"r".
Definition _rcu : ident := $"rcu".
Definition _rcu_head : ident := $"rcu_head".
Definition _receiving : ident := $"receiving".
Definition _receiving_counter : ident := $"receiving_counter".
Definition _refcount : ident := $"refcount".
Definition _remote_ephemeral : ident := $"remote_ephemeral".
Definition _remote_index : ident := $"remote_index".
Definition _remote_static : ident := $"remote_static".
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
Definition _src1 : ident := $"src1".
Definition _src2 : ident := $"src2".
Definition _state : ident := $"state".
Definition _static_identity : ident := $"static_identity".
Definition _static_private : ident := $"static_private".
Definition _static_public : ident := $"static_public".
Definition _t : ident := $"t".
Definition _table : ident := $"table".
Definition _timespec64 : ident := $"timespec64".
Definition _ts : ident := $"ts".
Definition _tv_nsec : ident := $"tv_nsec".
Definition _tv_sec : ident := $"tv_sec".
Definition _type : ident := $"type".
Definition _type_mask : ident := $"type_mask".
Definition _udp : ident := $"udp".
Definition _udphdr : ident := $"udphdr".
Definition _unused : ident := $"unused".
Definition _v : ident := $"v".
Definition _wg_birthdate_has_expired : ident := $"wg_birthdate_has_expired".
Definition _wg_device : ident := $"wg_device".
Definition _wg_index_hashtable_insert : ident := $"wg_index_hashtable_insert".
Definition _wg_index_hashtable_lookup : ident := $"wg_index_hashtable_lookup".
Definition _wg_index_hashtable_remove : ident := $"wg_index_hashtable_remove".
Definition _wg_index_hashtable_replace : ident := $"wg_index_hashtable_replace".
Definition _wg_peer : ident := $"wg_peer".
Definition _wg_peer_get_maybe_zero : ident := $"wg_peer_get_maybe_zero".
Definition _wg_peer_put : ident := $"wg_peer_put".
Definition _wg_pubkey_hashtable_lookup : ident := $"wg_pubkey_hashtable_lookup".
Definition _wg_ratelimiter_allow : ident := $"wg_ratelimiter_allow".
Definition _wg_shim_alloc_failures : ident := $"wg_shim_alloc_failures".
Definition _wg_shim_allocs : ident := $"wg_shim_allocs".
Definition _wg_shim_boottime_ns : ident := $"wg_shim_boottime_ns".
Definition _wg_shim_fail_next_alloc : ident := $"wg_shim_fail_next_alloc".
Definition _wg_shim_frees : ident := $"wg_shim_frees".
Definition _wg_shim_index_in_use : ident := $"wg_shim_index_in_use".
Definition _wg_shim_peer_release : ident := $"wg_shim_peer_release".
Definition _wg_shim_peer_released : ident := $"wg_shim_peer_released".
Definition _wg_shim_random_log : ident := $"wg_shim_random_log".
Definition _wg_shim_random_log_prev : ident := $"wg_shim_random_log_prev".
Definition _wg_shim_random_u32 : ident := $"wg_shim_random_u32".
Definition _wg_shim_ratelimit_allow : ident := $"wg_shim_ratelimit_allow".
Definition _wg_shim_real_nsec : ident := $"wg_shim_real_nsec".
Definition _wg_shim_real_sec : ident := $"wg_shim_real_sec".
Definition _wg_shim_refcount_dec_and_test : ident := $"wg_shim_refcount_dec_and_test".
Definition _wg_shim_refcount_inc : ident := $"wg_shim_refcount_inc".
Definition _wg_shim_refcount_inc_not_zero : ident := $"wg_shim_refcount_inc_not_zero".
Definition _wg_shim_refcount_neg : ident := $"wg_shim_refcount_neg".
Definition _wg_shim_refcount_warn : ident := $"wg_shim_refcount_warn".
Definition _wg_shim_refcount_warn_saturate : ident := $"wg_shim_refcount_warn_saturate".
Definition _x : ident := $"x".
Definition _y : ident := $"y".
Definition _t'1 : ident := 128%positive.
Definition _t'2 : ident := 129%positive.
Definition _t'3 : ident := 130%positive.
Definition _t'4 : ident := 131%positive.
Definition _t'5 : ident := 132%positive.
Definition _t'6 : ident := 133%positive.

Definition v_wg_shim_boottime_ns := {|
  gvar_info := tulong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_real_sec := {|
  gvar_info := tlong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_real_nsec := {|
  gvar_info := tlong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_ktime_get_coarse_boottime_ns := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar _wg_shim_boottime_ns tulong))
  (Sreturn (Some (Etempvar _t'1 tulong))))
|}.

Definition f_ktime_get_real_ts64 := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_ts, (tptr (Tstruct _timespec64 noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tlong) :: (_t'1, tlong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'2 (Evar _wg_shim_real_sec tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _ts (tptr (Tstruct _timespec64 noattr)))
          (Tstruct _timespec64 noattr)) _tv_sec tlong) (Etempvar _t'2 tlong)))
  (Ssequence
    (Sset _t'1 (Evar _wg_shim_real_nsec tlong))
    (Sassign
      (Efield
        (Ederef (Etempvar _ts (tptr (Tstruct _timespec64 noattr)))
          (Tstruct _timespec64 noattr)) _tv_nsec tlong)
      (Etempvar _t'1 tlong))))
|}.

Definition v_wg_shim_random_log := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_random_log_prev := {|
  gvar_info := (tarray tuchar 32);
  gvar_init := (Init_space 32 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_random_u32 := {|
  gvar_info := tuint;
  gvar_init := (Init_space 4 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_get_random_bytes := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_buf, (tptr tvoid)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_b, (tptr tuchar)) :: (_i, tulong) :: (_t'1, tint) ::
               (_t'3, tuchar) :: (_t'2, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _b (Ecast (Etempvar _buf (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Scall None
      (Evar _nondet_bytes (Tfunction ((tptr tuchar) :: tulong :: nil) tvoid
                            cc_default))
      ((Etempvar _b (tptr tuchar)) :: (Etempvar _len tulong) :: nil))
    (Ssequence
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                           (Econst_int (Int.repr 32) tint) tint)
              Sskip
              Sbreak)
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Ebinop Oadd (Evar _wg_shim_random_log (tarray tuchar 32))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd
                    (Evar _wg_shim_random_log_prev (tarray tuchar 32))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar)
                (Etempvar _t'3 tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong))))
      (Ssequence
        (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
        (Sloop
          (Ssequence
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                             (Etempvar _len tulong) tint)
                (Sset _t'1
                  (Ecast
                    (Ebinop Olt (Etempvar _i tulong)
                      (Econst_int (Int.repr 32) tint) tint) tbool))
                (Sset _t'1 (Econst_int (Int.repr 0) tint)))
              (Sifthenelse (Etempvar _t'1 tint) Sskip Sbreak))
            (Ssequence
              (Sset _t'2
                (Ederef
                  (Ebinop Oadd (Etempvar _b (tptr tuchar))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar))
              (Sassign
                (Ederef
                  (Ebinop Oadd (Evar _wg_shim_random_log (tarray tuchar 32))
                    (Etempvar _i tulong) (tptr tuchar)) tuchar)
                (Etempvar _t'2 tuchar))))
          (Sset _i
            (Ebinop Oadd (Etempvar _i tulong) (Econst_int (Int.repr 1) tint)
              tulong)))))))
|}.

Definition f_get_random_bytes_wait := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_buf, (tptr tvoid)) :: (_len, tulong) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None
  (Evar _get_random_bytes (Tfunction ((tptr tvoid) :: tulong :: nil) tvoid
                            cc_default))
  ((Etempvar _buf (tptr tvoid)) :: (Etempvar _len tulong) :: nil))
|}.

Definition f_get_random_u32 := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := nil;
  fn_vars := nil;
  fn_temps := ((_t'1, tuint) :: (_t'2, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Scall (Some _t'1) (Evar _nondet_u32 (Tfunction nil tuint cc_default))
      nil)
    (Sassign (Evar _wg_shim_random_u32 tuint) (Etempvar _t'1 tuint)))
  (Ssequence
    (Sset _t'2 (Evar _wg_shim_random_u32 tuint))
    (Sreturn (Some (Etempvar _t'2 tuint)))))
|}.

Definition v_wg_shim_allocs := {|
  gvar_info := tulong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_alloc_failures := {|
  gvar_info := tulong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_frees := {|
  gvar_info := tulong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition v_wg_shim_fail_next_alloc := {|
  gvar_info := tbool;
  gvar_init := (Init_space 1 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_kzalloc := {|
  fn_return := (tptr tvoid);
  fn_callconv := cc_default;
  fn_params := ((_size, tulong) :: (_flags, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_p, (tptr tvoid)) :: (_t'1, (tptr tvoid)) ::
               (_t'5, tulong) :: (_t'4, tbool) :: (_t'3, tulong) ::
               (_t'2, tulong) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'4 (Evar _wg_shim_fail_next_alloc tbool))
    (Sifthenelse (Etempvar _t'4 tbool)
      (Ssequence
        (Sassign (Evar _wg_shim_fail_next_alloc tbool)
          (Econst_int (Int.repr 0) tint))
        (Ssequence
          (Ssequence
            (Sset _t'5 (Evar _wg_shim_alloc_failures tulong))
            (Sassign (Evar _wg_shim_alloc_failures tulong)
              (Ebinop Oadd (Etempvar _t'5 tulong)
                (Econst_int (Int.repr 1) tint) tulong)))
          (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
      Sskip))
  (Ssequence
    (Ssequence
      (Scall (Some _t'1)
        (Evar _calloc (Tfunction (tulong :: tulong :: nil) (tptr tvoid)
                        cc_default))
        ((Econst_int (Int.repr 1) tint) :: (Etempvar _size tulong) :: nil))
      (Sset _p (Etempvar _t'1 (tptr tvoid))))
    (Ssequence
      (Sifthenelse (Etempvar _p (tptr tvoid))
        (Ssequence
          (Sset _t'3 (Evar _wg_shim_allocs tulong))
          (Sassign (Evar _wg_shim_allocs tulong)
            (Ebinop Oadd (Etempvar _t'3 tulong)
              (Econst_int (Int.repr 1) tint) tulong)))
        (Ssequence
          (Sset _t'2 (Evar _wg_shim_alloc_failures tulong))
          (Sassign (Evar _wg_shim_alloc_failures tulong)
            (Ebinop Oadd (Etempvar _t'2 tulong)
              (Econst_int (Int.repr 1) tint) tulong))))
      (Sreturn (Some (Etempvar _p (tptr tvoid)))))))
|}.

Definition f_kfree := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Sifthenelse (Etempvar _p (tptr tvoid))
  (Ssequence
    (Ssequence
      (Sset _t'1 (Evar _wg_shim_frees tulong))
      (Sassign (Evar _wg_shim_frees tulong)
        (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
          tulong)))
    (Scall None
      (Evar _quickproof_free (Tfunction ((tptr tvoid) :: nil) tvoid
                               cc_default))
      ((Ecast (Etempvar _p (tptr tvoid)) (tptr tvoid)) :: nil)))
  Sskip)
|}.

Definition f_kfree_sensitive := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_p, (tptr tvoid)) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Scall None (Evar _kfree (Tfunction ((tptr tvoid) :: nil) tvoid cc_default))
  ((Etempvar _p (tptr tvoid)) :: nil))
|}.

Definition v_quickproof_zero_page := {|
  gvar_info := (tarray tuchar 64);
  gvar_init := (Init_space 64 :: nil);
  gvar_readonly := true;
  gvar_volatile := false
|}.

Definition f___crypto_memneq := {|
  fn_return := tulong;
  fn_callconv := cc_default;
  fn_params := ((_a, (tptr tvoid)) :: (_b, (tptr tvoid)) ::
                (_size, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_x, (tptr tuchar)) :: (_y, (tptr tuchar)) ::
               (_neq, tulong) :: (_i, tulong) :: (_t'2, tuchar) ::
               (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _x (Ecast (Etempvar _a (tptr tvoid)) (tptr tuchar)))
  (Ssequence
    (Sset _y (Ecast (Etempvar _b (tptr tvoid)) (tptr tuchar)))
    (Ssequence
      (Sset _neq (Ecast (Econst_int (Int.repr 0) tint) tulong))
      (Ssequence
        (Ssequence
          (Sset _i (Ecast (Econst_int (Int.repr 0) tint) tulong))
          (Sloop
            (Ssequence
              (Sifthenelse (Ebinop Olt (Etempvar _i tulong)
                             (Etempvar _size tulong) tint)
                Sskip
                Sbreak)
              (Ssequence
                (Sset _t'1
                  (Ederef
                    (Ebinop Oadd (Etempvar _x (tptr tuchar))
                      (Etempvar _i tulong) (tptr tuchar)) tuchar))
                (Ssequence
                  (Sset _t'2
                    (Ederef
                      (Ebinop Oadd (Etempvar _y (tptr tuchar))
                        (Etempvar _i tulong) (tptr tuchar)) tuchar))
                  (Sset _neq
                    (Ebinop Oor (Etempvar _neq tulong)
                      (Ecast
                        (Ebinop Oxor (Etempvar _t'1 tuchar)
                          (Etempvar _t'2 tuchar) tint) tulong) tulong)))))
            (Sset _i
              (Ebinop Oadd (Etempvar _i tulong)
                (Econst_int (Int.repr 1) tint) tulong))))
        (Sreturn (Some (Etempvar _neq tulong)))))))
|}.

Definition f___crypto_xor := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_dst, (tptr tuchar)) :: (_src1, (tptr tuchar)) ::
                (_src2, (tptr tuchar)) :: (_len, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_i, tuint) :: (_t'2, tuchar) :: (_t'1, tuchar) :: nil);
  fn_body :=
(Ssequence
  (Sset _i (Econst_int (Int.repr 0) tint))
  (Sloop
    (Ssequence
      (Sifthenelse (Ebinop Olt (Etempvar _i tuint) (Etempvar _len tuint)
                     tint)
        Sskip
        Sbreak)
      (Ssequence
        (Sset _t'1
          (Ederef
            (Ebinop Oadd (Etempvar _src1 (tptr tuchar)) (Etempvar _i tuint)
              (tptr tuchar)) tuchar))
        (Ssequence
          (Sset _t'2
            (Ederef
              (Ebinop Oadd (Etempvar _src2 (tptr tuchar)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar))
          (Sassign
            (Ederef
              (Ebinop Oadd (Etempvar _dst (tptr tuchar)) (Etempvar _i tuint)
                (tptr tuchar)) tuchar)
            (Ebinop Oxor (Etempvar _t'1 tuchar) (Etempvar _t'2 tuchar) tint)))))
    (Sset _i
      (Ebinop Oadd (Etempvar _i tuint) (Econst_int (Int.repr 1) tint) tuint))))
|}.

Definition v_wg_shim_refcount_warn := {|
  gvar_info := (tarray tulong 5);
  gvar_init := (Init_space 40 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_wg_shim_refcount_warn_saturate := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: (_t, tint) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sassign (Ederef (Etempvar _r (tptr tuint)) tuint)
    (Econst_int (Int.repr (-1073741824)) tuint))
  (Ssequence
    (Sset _t'1
      (Ederef
        (Ebinop Oadd (Evar _wg_shim_refcount_warn (tarray tulong 5))
          (Etempvar _t tint) (tptr tulong)) tulong))
    (Sassign
      (Ederef
        (Ebinop Oadd (Evar _wg_shim_refcount_warn (tarray tulong 5))
          (Etempvar _t tint) (tptr tulong)) tulong)
      (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
        tulong))))
|}.

Definition f_wg_shim_refcount_neg := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_v, tuint) :: nil);
  fn_vars := nil;
  fn_temps := nil;
  fn_body :=
(Sreturn (Some (Ebinop Oge (Etempvar _v tuint)
                 (Econst_int (Int.repr (-2147483648)) tuint) tint)))
|}.

Definition f_wg_shim_refcount_inc_not_zero := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_old, tuint) :: (_t'3, tbool) :: (_t'2, tint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _old (Ederef (Etempvar _r (tptr tuint)) tuint))
  (Ssequence
    (Sifthenelse (Ebinop Oeq (Etempvar _old tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip)
    (Ssequence
      (Sassign (Ederef (Etempvar _r (tptr tuint)) tuint)
        (Ebinop Oadd (Etempvar _old tuint) (Econst_int (Int.repr 1) tuint)
          tuint))
      (Ssequence
        (Ssequence
          (Ssequence
            (Scall (Some _t'1)
              (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                            cc_default))
              ((Etempvar _old tuint) :: nil))
            (Sifthenelse (Etempvar _t'1 tbool)
              (Sset _t'2 (Econst_int (Int.repr 1) tint))
              (Ssequence
                (Scall (Some _t'3)
                  (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                                cc_default))
                  ((Ebinop Oadd (Etempvar _old tuint)
                     (Econst_int (Int.repr 1) tuint) tuint) :: nil))
                (Sset _t'2 (Ecast (Etempvar _t'3 tbool) tbool)))))
          (Sifthenelse (Etempvar _t'2 tint)
            (Scall None
              (Evar _wg_shim_refcount_warn_saturate (Tfunction
                                                      ((tptr tuint) ::
                                                       tint :: nil) tvoid
                                                      cc_default))
              ((Etempvar _r (tptr tuint)) ::
               (Econst_int (Int.repr 0) tint) :: nil))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 1) tint)))))))
|}.

Definition f_wg_shim_refcount_inc := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_old, tuint) :: (_t'3, tbool) :: (_t'2, tint) ::
               (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _old (Ederef (Etempvar _r (tptr tuint)) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _r (tptr tuint)) tuint)
      (Ebinop Oadd (Etempvar _old tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Sifthenelse (Ebinop Oeq (Etempvar _old tuint)
                   (Econst_int (Int.repr 0) tint) tint)
      (Scall None
        (Evar _wg_shim_refcount_warn_saturate (Tfunction
                                                ((tptr tuint) :: tint :: nil)
                                                tvoid cc_default))
        ((Etempvar _r (tptr tuint)) :: (Econst_int (Int.repr 2) tint) :: nil))
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                          cc_default))
            ((Etempvar _old tuint) :: nil))
          (Sifthenelse (Etempvar _t'1 tbool)
            (Sset _t'2 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall (Some _t'3)
                (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                              cc_default))
                ((Ebinop Oadd (Etempvar _old tuint)
                   (Econst_int (Int.repr 1) tuint) tuint) :: nil))
              (Sset _t'2 (Ecast (Etempvar _t'3 tbool) tbool)))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Scall None
            (Evar _wg_shim_refcount_warn_saturate (Tfunction
                                                    ((tptr tuint) :: tint ::
                                                     nil) tvoid cc_default))
            ((Etempvar _r (tptr tuint)) :: (Econst_int (Int.repr 1) tint) ::
             nil))
          Sskip)))))
|}.

Definition f_wg_shim_refcount_dec_and_test := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_r, (tptr tuint)) :: nil);
  fn_vars := nil;
  fn_temps := ((_old, tuint) :: (_t'4, tbool) :: (_t'3, tint) ::
               (_t'2, tint) :: (_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _old (Ederef (Etempvar _r (tptr tuint)) tuint))
  (Ssequence
    (Sassign (Ederef (Etempvar _r (tptr tuint)) tuint)
      (Ebinop Osub (Etempvar _old tuint) (Econst_int (Int.repr 1) tuint)
        tuint))
    (Ssequence
      (Ssequence
        (Ssequence
          (Scall (Some _t'1)
            (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                          cc_default))
            ((Etempvar _old tuint) :: nil))
          (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tbool) tint)
            (Sset _t'2
              (Ecast
                (Ebinop Oeq (Etempvar _old tuint)
                  (Econst_int (Int.repr 1) tuint) tint) tbool))
            (Sset _t'2 (Econst_int (Int.repr 0) tint))))
        (Sifthenelse (Etempvar _t'2 tint)
          (Sreturn (Some (Econst_int (Int.repr 1) tint)))
          Sskip))
      (Ssequence
        (Ssequence
          (Sifthenelse (Ebinop Oeq (Etempvar _old tuint)
                         (Econst_int (Int.repr 0) tint) tint)
            (Sset _t'3 (Econst_int (Int.repr 1) tint))
            (Ssequence
              (Scall (Some _t'4)
                (Evar _wg_shim_refcount_neg (Tfunction (tuint :: nil) tbool
                                              cc_default))
                ((Etempvar _old tuint) :: nil))
              (Sset _t'3 (Ecast (Etempvar _t'4 tbool) tbool))))
          (Sifthenelse (Etempvar _t'3 tint)
            (Scall None
              (Evar _wg_shim_refcount_warn_saturate (Tfunction
                                                      ((tptr tuint) ::
                                                       tint :: nil) tvoid
                                                      cc_default))
              ((Etempvar _r (tptr tuint)) ::
               (Econst_int (Int.repr 3) tint) :: nil))
            Sskip))
        (Sreturn (Some (Econst_int (Int.repr 0) tint)))))))
|}.

Definition v_wg_shim_peer_released := {|
  gvar_info := tulong;
  gvar_init := (Init_space 8 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_wg_peer_get_maybe_zero := {|
  fn_return := (tptr (Tstruct _wg_peer noattr));
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tbool) :: (_t'1, tint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sifthenelse (Eunop Onotbool
                   (Etempvar _peer (tptr (Tstruct _wg_peer noattr))) tint)
      (Sset _t'1 (Econst_int (Int.repr 1) tint))
      (Ssequence
        (Scall (Some _t'2)
          (Evar _wg_shim_refcount_inc_not_zero (Tfunction
                                                 ((tptr tuint) :: nil) tbool
                                                 cc_default))
          ((Eaddrof
             (Efield
               (Efield
                 (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                   (Tstruct _wg_peer noattr)) _refcount
                 (Tstruct _kref noattr)) _refcount tuint) (tptr tuint)) ::
           nil))
        (Sset _t'1 (Ecast (Eunop Onotbool (Etempvar _t'2 tbool) tint) tbool))))
    (Sifthenelse (Etempvar _t'1 tint)
      (Sreturn (Some (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))
      Sskip))
  (Sreturn (Some (Etempvar _peer (tptr (Tstruct _wg_peer noattr))))))
|}.

Definition f_wg_shim_peer_release := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_refcount, (tptr (Tstruct _kref noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar _wg_shim_peer_released tulong))
  (Sassign (Evar _wg_shim_peer_released tulong)
    (Ebinop Oadd (Etempvar _t'1 tulong) (Econst_int (Int.repr 1) tint)
      tulong)))
|}.

Definition f_wg_peer_put := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_peer, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sifthenelse (Eunop Onotbool
                 (Etempvar _peer (tptr (Tstruct _wg_peer noattr))) tint)
    (Sreturn None)
    Sskip)
  (Sloop
    (Ssequence
      (Scall (Some _t'1)
        (Evar _wg_shim_refcount_dec_and_test (Tfunction ((tptr tuint) :: nil)
                                               tbool cc_default))
        ((Eaddrof
           (Efield
             (Efield
               (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                 (Tstruct _wg_peer noattr)) _refcount (Tstruct _kref noattr))
             _refcount tuint) (tptr tuint)) :: nil))
      (Sifthenelse (Etempvar _t'1 tbool)
        (Scall None
          (Evar _wg_shim_peer_release (Tfunction
                                        ((tptr (Tstruct _kref noattr)) ::
                                         nil) tvoid cc_default))
          ((Eaddrof
             (Efield
               (Ederef (Etempvar _peer (tptr (Tstruct _wg_peer noattr)))
                 (Tstruct _wg_peer noattr)) _refcount (Tstruct _kref noattr))
             (tptr (Tstruct _kref noattr))) :: nil))
        Sskip))
    Sbreak))
|}.

Definition f_wg_pubkey_hashtable_lookup := {|
  fn_return := (tptr (Tstruct _wg_peer noattr));
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _pubkey_hashtable noattr))) ::
                (_pubkey, (tptr tuchar)) :: nil);
  fn_vars := nil;
  fn_temps := ((_iter_peer, (tptr (Tstruct _wg_peer noattr))) ::
               (_peer, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'2, (tptr (Tstruct _wg_peer noattr))) :: (_t'1, tint) ::
               nil);
  fn_body :=
(Ssequence
  (Sset _peer (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sset _iter_peer
        (Efield
          (Ederef (Etempvar _table (tptr (Tstruct _pubkey_hashtable noattr)))
            (Tstruct _pubkey_hashtable noattr)) _head
          (tptr (Tstruct _wg_peer noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _iter_peer (tptr (Tstruct _wg_peer noattr)))
            Sskip
            Sbreak)
          (Ssequence
            (Scall (Some _t'1)
              (Evar _memcmp (Tfunction
                              ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil)
                              tint cc_default))
              ((Etempvar _pubkey (tptr tuchar)) ::
               (Efield
                 (Efield
                   (Ederef
                     (Etempvar _iter_peer (tptr (Tstruct _wg_peer noattr)))
                     (Tstruct _wg_peer noattr)) _handshake
                   (Tstruct _noise_handshake noattr)) _remote_static
                 (tarray tuchar 32)) :: (Econst_int (Int.repr 32) tint) ::
               nil))
            (Sifthenelse (Eunop Onotbool (Etempvar _t'1 tint) tint)
              (Ssequence
                (Sset _peer
                  (Etempvar _iter_peer (tptr (Tstruct _wg_peer noattr))))
                Sbreak)
              Sskip)))
        (Sset _iter_peer
          (Efield
            (Ederef (Etempvar _iter_peer (tptr (Tstruct _wg_peer noattr)))
              (Tstruct _wg_peer noattr)) _pubkey_next
            (tptr (Tstruct _wg_peer noattr))))))
    (Ssequence
      (Scall (Some _t'2)
        (Evar _wg_peer_get_maybe_zero (Tfunction
                                        ((tptr (Tstruct _wg_peer noattr)) ::
                                         nil)
                                        (tptr (Tstruct _wg_peer noattr))
                                        cc_default))
        ((Etempvar _peer (tptr (Tstruct _wg_peer noattr))) :: nil))
      (Sreturn (Some (Etempvar _t'2 (tptr (Tstruct _wg_peer noattr))))))))
|}.

Definition f_wg_index_hashtable_remove := {|
  fn_return := tvoid;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _index_hashtable noattr))) ::
                (_entry, (tptr (Tstruct _index_hashtable_entry noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_link, (tptr (tptr (Tstruct _index_hashtable_entry noattr)))) ::
               (_t'5, tbool) ::
               (_t'4, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'3, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'2, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'1, (tptr (Tstruct _index_hashtable_entry noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'5
      (Efield
        (Ederef
          (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
          (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'5 tbool) tint)
      (Sreturn None)
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _link
        (Eaddrof
          (Efield
            (Ederef
              (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
              (Tstruct _index_hashtable noattr)) _head
            (tptr (Tstruct _index_hashtable_entry noattr)))
          (tptr (tptr (Tstruct _index_hashtable_entry noattr)))))
      (Sloop
        (Ssequence
          (Ssequence
            (Sset _t'4
              (Ederef
                (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                (tptr (Tstruct _index_hashtable_entry noattr))))
            (Sifthenelse (Etempvar _t'4 (tptr (Tstruct _index_hashtable_entry noattr)))
              Sskip
              Sbreak))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                (tptr (Tstruct _index_hashtable_entry noattr))))
            (Sifthenelse (Ebinop Oeq
                           (Etempvar _t'2 (tptr (Tstruct _index_hashtable_entry noattr)))
                           (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                           tint)
              (Ssequence
                (Ssequence
                  (Sset _t'3
                    (Efield
                      (Ederef
                        (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                        (Tstruct _index_hashtable_entry noattr)) _next
                      (tptr (Tstruct _index_hashtable_entry noattr))))
                  (Sassign
                    (Ederef
                      (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                      (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Etempvar _t'3 (tptr (Tstruct _index_hashtable_entry noattr)))))
                Sbreak)
              Sskip)))
        (Ssequence
          (Sset _t'1
            (Ederef
              (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
              (tptr (Tstruct _index_hashtable_entry noattr))))
          (Sset _link
            (Eaddrof
              (Efield
                (Ederef
                  (Etempvar _t'1 (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _next
                (tptr (Tstruct _index_hashtable_entry noattr)))
              (tptr (tptr (Tstruct _index_hashtable_entry noattr))))))))
    (Ssequence
      (Sassign
        (Efield
          (Ederef
            (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
            (Tstruct _index_hashtable_entry noattr)) _next
          (tptr (Tstruct _index_hashtable_entry noattr)))
        (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
      (Sassign
        (Efield
          (Ederef
            (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
            (Tstruct _index_hashtable_entry noattr)) _hashed tbool)
        (Econst_int (Int.repr 0) tint)))))
|}.

Definition f_wg_shim_index_in_use := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _index_hashtable noattr))) ::
                (_index, tuint) :: nil);
  fn_vars := nil;
  fn_temps := ((_e, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'1, tuint) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _e
      (Efield
        (Ederef (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
          (Tstruct _index_hashtable noattr)) _head
        (tptr (Tstruct _index_hashtable_entry noattr))))
    (Sloop
      (Ssequence
        (Sifthenelse (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
          Sskip
          Sbreak)
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _index tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar _t'1 tuint)
                         (Etempvar _index tuint) tint)
            (Sreturn (Some (Econst_int (Int.repr 1) tint)))
            Sskip)))
      (Sset _e
        (Efield
          (Ederef
            (Etempvar _e (tptr (Tstruct _index_hashtable_entry noattr)))
            (Tstruct _index_hashtable_entry noattr)) _next
          (tptr (Tstruct _index_hashtable_entry noattr))))))
  (Sreturn (Some (Econst_int (Int.repr 0) tint))))
|}.

Definition f_wg_index_hashtable_insert := {|
  fn_return := tuint;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _index_hashtable noattr))) ::
                (_entry, (tptr (Tstruct _index_hashtable_entry noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_t'2, tuint) :: (_t'1, tbool) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'3, tuint) :: nil);
  fn_body :=
(Ssequence
  (Scall None
    (Evar _wg_index_hashtable_remove (Tfunction
                                       ((tptr (Tstruct _index_hashtable noattr)) ::
                                        (tptr (Tstruct _index_hashtable_entry noattr)) ::
                                        nil) tvoid cc_default))
    ((Etempvar _table (tptr (Tstruct _index_hashtable noattr))) ::
     (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr))) :: nil))
  (Ssequence
    (Sloop
      (Ssequence
        (Scall (Some _t'2)
          (Evar _get_random_u32 (Tfunction nil tuint cc_default)) nil)
        (Sassign
          (Efield
            (Ederef
              (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _index tuint)
          (Ecast (Etempvar _t'2 tuint) tuint)))
      (Ssequence
        (Ssequence
          (Sset _t'5
            (Efield
              (Ederef
                (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _index tuint))
          (Scall (Some _t'1)
            (Evar _wg_shim_index_in_use (Tfunction
                                          ((tptr (Tstruct _index_hashtable noattr)) ::
                                           tuint :: nil) tbool cc_default))
            ((Etempvar _table (tptr (Tstruct _index_hashtable noattr))) ::
             (Etempvar _t'5 tuint) :: nil)))
        (Sifthenelse (Etempvar _t'1 tbool) Sskip Sbreak)))
    (Ssequence
      (Ssequence
        (Sset _t'4
          (Efield
            (Ederef
              (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
              (Tstruct _index_hashtable noattr)) _head
            (tptr (Tstruct _index_hashtable_entry noattr))))
        (Sassign
          (Efield
            (Ederef
              (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr)))
          (Etempvar _t'4 (tptr (Tstruct _index_hashtable_entry noattr)))))
      (Ssequence
        (Sassign
          (Efield
            (Ederef
              (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _hashed tbool)
          (Econst_int (Int.repr 1) tint))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
                (Tstruct _index_hashtable noattr)) _head
              (tptr (Tstruct _index_hashtable_entry noattr)))
            (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr))))
          (Ssequence
            (Sset _t'3
              (Efield
                (Ederef
                  (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _index tuint))
            (Sreturn (Some (Etempvar _t'3 tuint)))))))))
|}.

Definition f_wg_index_hashtable_replace := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _index_hashtable noattr))) ::
                (_old, (tptr (Tstruct _index_hashtable_entry noattr))) ::
                (_new, (tptr (Tstruct _index_hashtable_entry noattr))) ::
                nil);
  fn_vars := nil;
  fn_temps := ((_link, (tptr (tptr (Tstruct _index_hashtable_entry noattr)))) ::
               (_t'6, tbool) :: (_t'5, tuint) ::
               (_t'4, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'3, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'2, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'1, (tptr (Tstruct _index_hashtable_entry noattr))) :: nil);
  fn_body :=
(Ssequence
  (Ssequence
    (Sset _t'6
      (Efield
        (Ederef
          (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
          (Tstruct _index_hashtable_entry noattr)) _hashed tbool))
    (Sifthenelse (Eunop Onotbool (Etempvar _t'6 tbool) tint)
      (Sreturn (Some (Econst_int (Int.repr 0) tint)))
      Sskip))
  (Ssequence
    (Ssequence
      (Sset _t'5
        (Efield
          (Ederef
            (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
            (Tstruct _index_hashtable_entry noattr)) _index tuint))
      (Sassign
        (Efield
          (Ederef
            (Etempvar _new (tptr (Tstruct _index_hashtable_entry noattr)))
            (Tstruct _index_hashtable_entry noattr)) _index tuint)
        (Etempvar _t'5 tuint)))
    (Ssequence
      (Ssequence
        (Sset _link
          (Eaddrof
            (Efield
              (Ederef
                (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
                (Tstruct _index_hashtable noattr)) _head
              (tptr (Tstruct _index_hashtable_entry noattr)))
            (tptr (tptr (Tstruct _index_hashtable_entry noattr)))))
        (Sloop
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Ederef
                  (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                  (tptr (Tstruct _index_hashtable_entry noattr))))
              (Sifthenelse (Etempvar _t'4 (tptr (Tstruct _index_hashtable_entry noattr)))
                Sskip
                Sbreak))
            (Ssequence
              (Sset _t'3
                (Ederef
                  (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                  (tptr (Tstruct _index_hashtable_entry noattr))))
              (Sifthenelse (Ebinop Oeq
                             (Etempvar _t'3 (tptr (Tstruct _index_hashtable_entry noattr)))
                             (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
                             tint)
                (Ssequence
                  (Sassign
                    (Ederef
                      (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                      (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Etempvar _new (tptr (Tstruct _index_hashtable_entry noattr))))
                  Sbreak)
                Sskip)))
          (Ssequence
            (Sset _t'2
              (Ederef
                (Etempvar _link (tptr (tptr (Tstruct _index_hashtable_entry noattr))))
                (tptr (Tstruct _index_hashtable_entry noattr))))
            (Sset _link
              (Eaddrof
                (Efield
                  (Ederef
                    (Etempvar _t'2 (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Tstruct _index_hashtable_entry noattr)) _next
                  (tptr (Tstruct _index_hashtable_entry noattr)))
                (tptr (tptr (Tstruct _index_hashtable_entry noattr))))))))
      (Ssequence
        (Ssequence
          (Sset _t'1
            (Efield
              (Ederef
                (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _next
              (tptr (Tstruct _index_hashtable_entry noattr))))
          (Sassign
            (Efield
              (Ederef
                (Etempvar _new (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _next
              (tptr (Tstruct _index_hashtable_entry noattr)))
            (Etempvar _t'1 (tptr (Tstruct _index_hashtable_entry noattr)))))
        (Ssequence
          (Sassign
            (Efield
              (Ederef
                (Etempvar _new (tptr (Tstruct _index_hashtable_entry noattr)))
                (Tstruct _index_hashtable_entry noattr)) _hashed tbool)
            (Econst_int (Int.repr 1) tint))
          (Ssequence
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _next
                (tptr (Tstruct _index_hashtable_entry noattr)))
              (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
            (Ssequence
              (Sassign
                (Efield
                  (Ederef
                    (Etempvar _old (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Tstruct _index_hashtable_entry noattr)) _hashed tbool)
                (Econst_int (Int.repr 0) tint))
              (Sreturn (Some (Econst_int (Int.repr 1) tint))))))))))
|}.

Definition f_wg_index_hashtable_lookup := {|
  fn_return := (tptr (Tstruct _index_hashtable_entry noattr));
  fn_callconv := cc_default;
  fn_params := ((_table, (tptr (Tstruct _index_hashtable noattr))) ::
                (_type_mask, tint) :: (_index, tuint) ::
                (_peer, (tptr (tptr (Tstruct _wg_peer noattr)))) :: nil);
  fn_vars := nil;
  fn_temps := ((_iter_entry, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_entry, (tptr (Tstruct _index_hashtable_entry noattr))) ::
               (_t'1, (tptr (Tstruct _wg_peer noattr))) :: (_t'6, tint) ::
               (_t'5, tuint) :: (_t'4, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'3, (tptr (Tstruct _wg_peer noattr))) ::
               (_t'2, (tptr (Tstruct _wg_peer noattr))) :: nil);
  fn_body :=
(Ssequence
  (Sset _entry (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
  (Ssequence
    (Ssequence
      (Sset _iter_entry
        (Efield
          (Ederef (Etempvar _table (tptr (Tstruct _index_hashtable noattr)))
            (Tstruct _index_hashtable noattr)) _head
          (tptr (Tstruct _index_hashtable_entry noattr))))
      (Sloop
        (Ssequence
          (Sifthenelse (Etempvar _iter_entry (tptr (Tstruct _index_hashtable_entry noattr)))
            Sskip
            Sbreak)
          (Ssequence
            (Sset _t'5
              (Efield
                (Ederef
                  (Etempvar _iter_entry (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _index tuint))
            (Sifthenelse (Ebinop Oeq (Etempvar _t'5 tuint)
                           (Etempvar _index tuint) tint)
              (Ssequence
                (Ssequence
                  (Sset _t'6
                    (Efield
                      (Ederef
                        (Etempvar _iter_entry (tptr (Tstruct _index_hashtable_entry noattr)))
                        (Tstruct _index_hashtable_entry noattr)) _type tint))
                  (Sifthenelse (Ebinop Oand (Etempvar _t'6 tint)
                                 (Etempvar _type_mask tint) tint)
                    (Sset _entry
                      (Etempvar _iter_entry (tptr (Tstruct _index_hashtable_entry noattr))))
                    Sskip))
                Sbreak)
              Sskip)))
        (Sset _iter_entry
          (Efield
            (Ederef
              (Etempvar _iter_entry (tptr (Tstruct _index_hashtable_entry noattr)))
              (Tstruct _index_hashtable_entry noattr)) _next
            (tptr (Tstruct _index_hashtable_entry noattr))))))
    (Ssequence
      (Sifthenelse (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
        (Ssequence
          (Ssequence
            (Ssequence
              (Sset _t'4
                (Efield
                  (Ederef
                    (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                    (Tstruct _index_hashtable_entry noattr)) _peer
                  (tptr (Tstruct _wg_peer noattr))))
              (Scall (Some _t'1)
                (Evar _wg_peer_get_maybe_zero (Tfunction
                                                ((tptr (Tstruct _wg_peer noattr)) ::
                                                 nil)
                                                (tptr (Tstruct _wg_peer noattr))
                                                cc_default))
                ((Etempvar _t'4 (tptr (Tstruct _wg_peer noattr))) :: nil)))
            (Sassign
              (Efield
                (Ederef
                  (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _peer
                (tptr (Tstruct _wg_peer noattr)))
              (Etempvar _t'1 (tptr (Tstruct _wg_peer noattr)))))
          (Ssequence
            (Sset _t'2
              (Efield
                (Ederef
                  (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                  (Tstruct _index_hashtable_entry noattr)) _peer
                (tptr (Tstruct _wg_peer noattr))))
            (Sifthenelse (Etempvar _t'2 (tptr (Tstruct _wg_peer noattr)))
              (Ssequence
                (Sset _t'3
                  (Efield
                    (Ederef
                      (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr)))
                      (Tstruct _index_hashtable_entry noattr)) _peer
                    (tptr (Tstruct _wg_peer noattr))))
                (Sassign
                  (Ederef
                    (Etempvar _peer (tptr (tptr (Tstruct _wg_peer noattr))))
                    (tptr (Tstruct _wg_peer noattr)))
                  (Etempvar _t'3 (tptr (Tstruct _wg_peer noattr)))))
              (Sset _entry
                (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid))))))
        Sskip)
      (Sreturn (Some (Etempvar _entry (tptr (Tstruct _index_hashtable_entry noattr))))))))
|}.

Definition v_wg_shim_ratelimit_allow := {|
  gvar_info := tbool;
  gvar_init := (Init_space 1 :: nil);
  gvar_readonly := false;
  gvar_volatile := false
|}.

Definition f_wg_ratelimiter_allow := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_skb, (tptr (Tstruct _sk_buff noattr))) ::
                (_net__1, (tptr (Tstruct _net noattr))) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tbool) :: nil);
  fn_body :=
(Ssequence
  (Sset _t'1 (Evar _wg_shim_ratelimit_allow tbool))
  (Sreturn (Some (Etempvar _t'1 tbool))))
|}.

Definition f_wg_birthdate_has_expired := {|
  fn_return := tbool;
  fn_callconv := cc_default;
  fn_params := ((_birthday_nanoseconds, tulong) ::
                (_expiration_seconds, tulong) :: nil);
  fn_vars := nil;
  fn_temps := ((_t'1, tulong) :: nil);
  fn_body :=
(Ssequence
  (Scall (Some _t'1)
    (Evar _ktime_get_coarse_boottime_ns (Tfunction nil tulong cc_default))
    nil)
  (Sreturn (Some (Ebinop Ole
                   (Ecast
                     (Ebinop Oadd (Etempvar _birthday_nanoseconds tulong)
                       (Ebinop Omul (Etempvar _expiration_seconds tulong)
                         (Econst_long (Int64.repr 1000000000) tlong) tulong)
                       tulong) tlong) (Ecast (Etempvar _t'1 tulong) tlong)
                   tint))))
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
 (_memcmp,
   Gfun(External (EF_external "memcmp"
                   (mksignature (AST.Xptr :: AST.Xptr :: AST.Xlong :: nil)
                     AST.Xint cc_default))
     ((tptr tvoid) :: (tptr tvoid) :: tulong :: nil) tint cc_default)) ::
 (_calloc,
   Gfun(External (EF_external "calloc"
                   (mksignature (AST.Xlong :: AST.Xlong :: nil) AST.Xptr
                     cc_default)) (tulong :: tulong :: nil) (tptr tvoid)
     cc_default)) ::
 (_quickproof_free,
   Gfun(External (EF_external "quickproof_free"
                   (mksignature (AST.Xptr :: nil) AST.Xvoid cc_default))
     ((tptr tvoid) :: nil) tvoid cc_default)) ::
 (_nondet_u32,
   Gfun(External (EF_external "nondet_u32"
                   (mksignature nil AST.Xint cc_default)) nil tuint
     cc_default)) ::
 (_nondet_bytes,
   Gfun(External (EF_external "nondet_bytes"
                   (mksignature (AST.Xptr :: AST.Xlong :: nil) AST.Xvoid
                     cc_default)) ((tptr tuchar) :: tulong :: nil) tvoid
     cc_default)) :: (_wg_shim_boottime_ns, Gvar v_wg_shim_boottime_ns) ::
 (_wg_shim_real_sec, Gvar v_wg_shim_real_sec) ::
 (_wg_shim_real_nsec, Gvar v_wg_shim_real_nsec) ::
 (_ktime_get_coarse_boottime_ns, Gfun(Internal f_ktime_get_coarse_boottime_ns)) ::
 (_ktime_get_real_ts64, Gfun(Internal f_ktime_get_real_ts64)) ::
 (_wg_shim_random_log, Gvar v_wg_shim_random_log) ::
 (_wg_shim_random_log_prev, Gvar v_wg_shim_random_log_prev) ::
 (_wg_shim_random_u32, Gvar v_wg_shim_random_u32) ::
 (_get_random_bytes, Gfun(Internal f_get_random_bytes)) ::
 (_get_random_bytes_wait, Gfun(Internal f_get_random_bytes_wait)) ::
 (_get_random_u32, Gfun(Internal f_get_random_u32)) ::
 (_wg_shim_allocs, Gvar v_wg_shim_allocs) ::
 (_wg_shim_alloc_failures, Gvar v_wg_shim_alloc_failures) ::
 (_wg_shim_frees, Gvar v_wg_shim_frees) ::
 (_wg_shim_fail_next_alloc, Gvar v_wg_shim_fail_next_alloc) ::
 (_kzalloc, Gfun(Internal f_kzalloc)) :: (_kfree, Gfun(Internal f_kfree)) ::
 (_kfree_sensitive, Gfun(Internal f_kfree_sensitive)) ::
 (_quickproof_zero_page, Gvar v_quickproof_zero_page) ::
 (___crypto_memneq, Gfun(Internal f___crypto_memneq)) ::
 (___crypto_xor, Gfun(Internal f___crypto_xor)) ::
 (_wg_shim_refcount_warn, Gvar v_wg_shim_refcount_warn) ::
 (_wg_shim_refcount_warn_saturate, Gfun(Internal f_wg_shim_refcount_warn_saturate)) ::
 (_wg_shim_refcount_neg, Gfun(Internal f_wg_shim_refcount_neg)) ::
 (_wg_shim_refcount_inc_not_zero, Gfun(Internal f_wg_shim_refcount_inc_not_zero)) ::
 (_wg_shim_refcount_inc, Gfun(Internal f_wg_shim_refcount_inc)) ::
 (_wg_shim_refcount_dec_and_test, Gfun(Internal f_wg_shim_refcount_dec_and_test)) ::
 (_wg_shim_peer_released, Gvar v_wg_shim_peer_released) ::
 (_wg_peer_get_maybe_zero, Gfun(Internal f_wg_peer_get_maybe_zero)) ::
 (_wg_shim_peer_release, Gfun(Internal f_wg_shim_peer_release)) ::
 (_wg_peer_put, Gfun(Internal f_wg_peer_put)) ::
 (_wg_pubkey_hashtable_lookup, Gfun(Internal f_wg_pubkey_hashtable_lookup)) ::
 (_wg_index_hashtable_remove, Gfun(Internal f_wg_index_hashtable_remove)) ::
 (_wg_shim_index_in_use, Gfun(Internal f_wg_shim_index_in_use)) ::
 (_wg_index_hashtable_insert, Gfun(Internal f_wg_index_hashtable_insert)) ::
 (_wg_index_hashtable_replace, Gfun(Internal f_wg_index_hashtable_replace)) ::
 (_wg_index_hashtable_lookup, Gfun(Internal f_wg_index_hashtable_lookup)) ::
 (_wg_shim_ratelimit_allow, Gvar v_wg_shim_ratelimit_allow) ::
 (_wg_ratelimiter_allow, Gfun(Internal f_wg_ratelimiter_allow)) ::
 (_wg_birthdate_has_expired, Gfun(Internal f_wg_birthdate_has_expired)) ::
 nil).

Definition public_idents : list ident :=
(_wg_birthdate_has_expired :: _wg_ratelimiter_allow ::
 _wg_shim_ratelimit_allow :: _wg_index_hashtable_lookup ::
 _wg_index_hashtable_replace :: _wg_index_hashtable_insert ::
 _wg_index_hashtable_remove :: _wg_pubkey_hashtable_lookup :: _wg_peer_put ::
 _wg_peer_get_maybe_zero :: _wg_shim_peer_released ::
 _wg_shim_refcount_dec_and_test :: _wg_shim_refcount_inc ::
 _wg_shim_refcount_inc_not_zero :: _wg_shim_refcount_warn :: ___crypto_xor ::
 ___crypto_memneq :: _quickproof_zero_page :: _kfree_sensitive :: _kfree ::
 _kzalloc :: _wg_shim_fail_next_alloc :: _wg_shim_frees ::
 _wg_shim_alloc_failures :: _wg_shim_allocs :: _get_random_u32 ::
 _get_random_bytes_wait :: _get_random_bytes :: _wg_shim_random_u32 ::
 _wg_shim_random_log_prev :: _wg_shim_random_log :: _ktime_get_real_ts64 ::
 _ktime_get_coarse_boottime_ns :: _wg_shim_real_nsec :: _wg_shim_real_sec ::
 _wg_shim_boottime_ns :: _nondet_bytes :: _nondet_u32 :: _quickproof_free ::
 _calloc :: _memcmp :: ___builtin_debug :: ___builtin_write32_reversed ::
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


