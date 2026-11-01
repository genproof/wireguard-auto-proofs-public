(* (common4 group kents, kents_snap): the straight-line body for one kent *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_cs.
Require Import WgNoise.proof.harness.common4.hc4_ctx.
Require Import WgNoise.proof.harness.common4.hc4b_ke_snap1.
Require WgNoise.harness.x_cookie_mac.code.
Local Open Scope logic.

(* the loop body of kents_snap after the test of l *)
Definition hc4b_ke_snap_stmt : statement :=
  Eval cbv beta iota zeta delta [HC.f_kents_snap fn_body] in
  match fn_body HC.f_kents_snap with Sloop (Ssequence _ s) _ => s | _ => Sskip end.

Section S.
Context {Espec: OracleKind}.
#[local] Existing Instance CS4.

Lemma hc4b_ke_snap_one_ok k sh E nxe h K lk r (FR: mpred) :
  readable_share sh -> is_pointer_or_null (e_peer E) -> is_pointer_or_null nxe -> kp_ok K ->
  field_compatible t_kent [] k ->
  semax (func_tycontext HC.f_kents_snap [] hc4_G_dev_take nil)
    (PROP () LOCAL (temp HC._l k)
     SEP (@field_at CS4 sh t_kp [StructField I._entry] (entry_val E nxe h) k; hc4b_ke_snap_kpo k K lk r;
          hc4b_ke_snap_blank k; FR))
    hc4b_ke_snap_stmt
    (normal_ret_assert (PROP () LOCAL (temp HC._l k)
     SEP (@field_at CS4 sh t_kp [StructField I._entry] (entry_val E nxe h) k; hc4b_ke_snap_kpo k K lk r;
          hc4b_ke_snap_full k E nxe h K; FR))).
Proof.
  intros RS PE PN KO FC.
  unfold hc4b_ke_snap_stmt. abbreviate_semax.
  unfold hc4b_ke_snap_kpo, hc4b_ke_snap_ss, hc4b_ke_snap_rs, hc4b_ke_snap_blank, entry_val.
  repeat flatten_sepcon_in_SEP.
  pose proof KO as (L1 & L2 & L3).
  forward.
  match goal with |- context [temp HC._kp ?v] => replace v with (offset_val 0 k) by reflexivity end.
  assert (Hk: isptr k) by (destruct FC; auto). rewrite isptr_offset_val_zero by auto.
  assert (FCK: field_compatible t_kp [] k).
  { assert (FC2: field_compatible t_kent [StructField HC._kp] k) by auto with field_compatible.
    apply field_compatible_nested_field in FC2. simpl in FC2.
    rewrite isptr_offset_val_zero in FC2 by auto. exact FC2. }
  do 8 forward.
  forward.
  { entailer!. destruct h; simpl; auto. }
  forward.
  forward_call (Ews, field_address t_kent (DOT HC._skey0) k, Ews,
                field_address t_kp [StructField I._key; StructField I._sending] k, sk_key (kp_send K)).
  { entailer!. rewrite L1. rewrite !field_address_offset by auto with field_compatible.
    destruct k; try contradiction. simpl. rewrite !Ptrofs.add_zero. reflexivity. }
  { rewrite L1. cancel. }
  forward_call (Ews, field_address t_kent (DOT HC._rkey0) k, Ews,
                field_address t_kp [StructField I._key; StructField I._receiving] k, sk_key (kp_recv K)).
  { entailer!. rewrite L2. rewrite !field_address_offset by auto with field_compatible.
    destruct k; try contradiction. simpl. rewrite !Ptrofs.add_zero. reflexivity. }
  { rewrite L2. cancel. }
  do 4 forward.
  forward. { entailer!. destruct (sk_valid (kp_send K)); simpl; auto. }
  forward.
  forward. { entailer!. destruct (sk_valid (kp_recv K)); simpl; auto. }
  forward.
  do 4 forward.
  freeze FZ := - (field_at Ews t_kp (DOT I._receiving_counter) _ k) (field_at_ Ews t_kent (DOT HC._bt0) k).
  unfold field_at_. change (default_val (nested_field_type t_kent (DOT HC._bt0))) with (Zrepeat Vundef 128).
  forward_for_simple_bound 128 (EX j: Z, PROP () LOCAL (temp HC._kp k; temp HC._l k)
    SEP (field_at Ews t_kp (DOT I._receiving_counter) (Vlong (kp_rcounter K), (lk, map Vlong (kp_backtrack K))) k;
         field_at Ews t_kent (DOT HC._bt0) (sublist 0 j (map Vlong (kp_backtrack K)) ++ Zrepeat Vundef (128 - j)) k;
         FRZL FZ))%assert.
  { entailer!. }
  { forward.
    forward.
    entailer!.
    apply derives_refl'. f_equal. list_solve. }
  rewrite sublist_same by (rewrite ?Zlength_map; lia). rewrite Z.sub_diag, Zrepeat_0, app_nil_r.
  thaw FZ.
  do 2 forward.
  forward. { entailer!. destruct (kp_init K); simpl; auto. }
  forward.
  do 4 forward.
  replace (force_val (sem_cast_i2bool (Val.of_bool h))) with (Val.of_bool h) by (destruct h; reflexivity).
  replace (force_val (sem_cast_i2bool (Val.of_bool (sk_valid (kp_send K))))) with (Val.of_bool (sk_valid (kp_send K)))
    by (destruct (sk_valid (kp_send K)); reflexivity).
  replace (force_val (sem_cast_i2bool (Val.of_bool (sk_valid (kp_recv K))))) with (Val.of_bool (sk_valid (kp_recv K)))
    by (destruct (sk_valid (kp_recv K)); reflexivity).
  replace (force_val (sem_cast_i2bool (Val.of_bool (kp_init K)))) with (Val.of_bool (kp_init K))
    by (destruct (kp_init K); reflexivity).
  entailer!.
  unfold hc4b_ke_snap_kpo, hc4b_ke_snap_ss, hc4b_ke_snap_rs, hc4b_ke_snap_full, entry_val.
  cancel.
Qed.

End S.
