(* law keypairs, segment Op0 branch L, piece 2a: statements 4..14 (the stores into node k: scnt, rcnt, kp, refs, held, initiator, remote_index (snap),
   birth, recv_valid / send_valid, bytes_copy send / recv).

   States: hkp5_segOp0_L_defs.v; "Op0 branch L". *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Export WgNoise.proof.harness.keypairs.hkp5_segOp0_L_defs.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require WgNoise.proof.harness.common.hc3_body_snap.
Require WgNoise.harness.x_handshake.code.

Module HB := WgNoise.proof.harness.common.hc3_body_snap.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

(* ---- helpers (prefix hkp5_o0L2a_; port of v1's hkp4_o0L2a_) ---- *)

#[local] Instance hkp5_o0L2a_cce : change_composite_env CSkh W_keypairs.
Proof. make_cs_preserve CSkh W_keypairs. Defined.

Lemma hkp5_o0L2a_snapcs : cs_preserve_type CSkh W_keypairs (@coeq _ _ hkp5_o0L2a_cce) t_hsnap = true.
Proof. vm_compute; reflexivity. Qed.

Lemma hkp5_o0L2a_ri_cs sh (v: val) s :
  @field_at CSkh sh t_hsnap (DOT WgNoise.harness.x_handshake.code._remote_index) v s =
  @field_at W_keypairs sh t_hsnap (DOT KC._remote_index) v s.
Proof.
  change KC._remote_index with WgNoise.harness.x_handshake.code._remote_index.
  exact (f_equal (fun f => f s) (@field_at_change_composite CSkh W_keypairs hkp5_o0L2a_cce sh t_hsnap
    (DOT WgNoise.harness.x_handshake.code._remote_index) v v (JMeq_refl v) hkp5_o0L2a_snapcs)).
Qed.

Lemma hkp5_o0L2a_wand_gen (A B R: mpred) : (B |-- A * R)%logic -> (R * A |-- B)%logic -> (B |-- A * (A -* B))%logic.
Proof.
  intros H1 H2. eapply derives_trans; [exact H1 |]. apply sepcon_derives; [apply derives_refl |].
  apply wand_sepcon_adjoint. exact H2.
Qed.

Ltac hkp5_o0L2a_remove A t :=
  match t with
  | sepcon ?X A => X
  | sepcon ?X ?Y => let X' := hkp5_o0L2a_remove A X in constr:(sepcon X' Y)
  end.

Lemma hkp5_o0L2a_snap_open sh sn s :
  @data_at HCS sh t_hsnap (hsnap_val sn) s |--
  @field_at W_keypairs sh t_hsnap (DOT KC._remote_index) (Vint (hs_rindex (sn_hs sn))) s *
  (@field_at W_keypairs sh t_hsnap (DOT KC._remote_index) (Vint (hs_rindex (sn_hs sn))) s -*
   @data_at HCS sh t_hsnap (hsnap_val sn) s)%logic.
Proof.
  destruct sn as [E nx hd H]. cbn [sn_hs].
  unfold hsnap_val. cbn [sn_entry sn_next sn_hashed sn_hs].
  rewrite HB.hc3b_snap_take_snap_eq.
  rewrite hkp5_o0L2a_ri_cs.
  match goal with |- ?B |-- sepcon ?A _ =>
    let R := hkp5_o0L2a_remove A B in apply (hkp5_o0L2a_wand_gen A B R); cancel end.
Qed.

(* the node struct mk field by field (unfold_data_at is very slow on it) *)
Lemma hkp5_o0L2a_mk_eq sh (a b c d e: val) (s r: list val) (f g h i j l m n o: val) k :
  data_at sh t_mk5 (a, (b, (c, (d, (e, (s, (r, (f, (g, (h, (i, (j, (l, (m, (n, o))))))))))))))) k =
  (field_at sh t_mk5 (DOT KC._kp) a k * field_at sh t_mk5 (DOT KC._refs) b k * spacer sh 12 16 k *
  field_at sh t_mk5 (DOT KC._held) c k *
  field_at sh t_mk5 (DOT KC._hashed) d k * spacer sh 25 28 k *
  field_at sh t_mk5 (DOT KC._index) e k *
  data_at sh (tarray tuchar 32) s (field_address t_mk5 (DOT KC._send) k) *
  data_at sh (tarray tuchar 32) r (field_address t_mk5 (DOT KC._recv) k) *
  field_at sh t_mk5 (DOT KC._send_valid) f k * field_at sh t_mk5 (DOT KC._recv_valid) g k *
  field_at sh t_mk5 (DOT KC._initiator) h k * spacer sh 99 100 k *
  field_at sh t_mk5 (DOT KC._remote_index) i k *
  field_at sh t_mk5 (DOT KC._birth) j k * field_at sh t_mk5 (DOT KC._id) l k *
  field_at sh t_mk5 (DOT KC._scnt) m k * field_at sh t_mk5 (DOT KC._rcnt) n k *
  field_at sh t_mk5 (DOT KC._next) o k)%logic.
Proof.
  match goal with |- data_at _ _ ?v _ = _ => set (V := v) end.
  unfold data_at. rewrite (@field_at_Tstruct W_keypairs sh t_mk5 [] KC._mk noattr V V k eq_refl (JMeq_refl _)).
  simpl co_members. lazy beta iota zeta delta [nested_sfieldlist_at].
  simpl struct_pred. unfold withspacer. simpl nested_field_offset. simpl sizeof.
  repeat match goal with |- context [Z.eq_dec ?x ?y] => destruct (Z.eq_dec x y); [try (exfalso; lia) | try (exfalso; lia)] end.
  subst V.
  rewrite (field_at_data_at sh t_mk5 (DOT KC._send)), (field_at_data_at sh t_mk5 (DOT KC._recv)).
  simpl nested_field_type.
  apply pred_ext; cancel.
Qed.

Lemma hkp5_o0L2a_sr_addr k : field_compatible t_mk5 (DOT KC._kp) k ->
  field_address t_mk5 (DOT KC._send) k = offset_val 32 k /\ field_address t_mk5 (DOT KC._recv) k = offset_val 64 k.
Proof.
  intros H. apply field_compatible_cons in H. destruct H as [_ H].
  split; (rewrite field_address_offset; [reflexivity | apply field_compatible_cons; split; [ | exact H]]);
    unfold in_members; simpl; auto 20.
Qed.

Lemma hkp5_o0L2a_mk_undef sh k :
  data_at_ sh t_mk5 k = data_at sh t_mk5 (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Zrepeat Vundef 32,
    (Zrepeat Vundef 32, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, Vundef))))))))))))))) k.
Proof. unfold data_at_, field_at_, data_at. reflexivity. Qed.

Lemma hkp5_o0L2a_hout sh n x : @data_at W_keypairs sh (tarray tuchar n) (Zrepeat Vundef n) x = hout sh n x.
Proof. unfold hout, data_at_, field_at_. apply HB.hc3b_snap_take_data_at_cs. Qed.

Lemma hkp5_o0L2a_hbytes sh A x : Zlength A = 32 ->
  hbytes sh A x = @data_at W_keypairs sh (tarray tuchar 32) (bytes A) x.
Proof. intros L. unfold hbytes. rewrite L. apply HB.hc3b_snap_take_data_at_cs. Qed.

Lemma hkp5_o0L2a_sel (b: bool) sh K1 K2 f1 f2 :
  (hbytes sh K1 f1 * hbytes sh K2 f2 |--
   hbytes sh (if b then K1 else K2) (if b then f1 else f2) * hbytes sh (if b then K2 else K1) (if b then f2 else f1))%logic.
Proof. destruct b; cancel. Qed.

Lemma hkp5_o0L2a_unsel (b: bool) sh K1 K2 f1 f2 :
  (hbytes sh (if b then K1 else K2) (if b then f1 else f2) * hbytes sh (if b then K2 else K1) (if b then f2 else f1) |--
   hbytes sh K1 f1 * hbytes sh K2 f2)%logic.
Proof. destruct b; cancel. Qed.

Lemma hkp5_o0L2a_i2bool b : force_val (sem_cast_i2bool (Val.of_bool b)) = Val.of_bool b.
Proof. destruct b; reflexivity. Qed.

(* the node after the stores and the two copies, back as one data_at with hkp5_o0L_kv1 *)
Lemma hkp5_o0L2a_node_fold (F: hkp5_fix) (O: hkp5_o0) k K1 K2 :
  K1 = kdf1 (hs_ck (p_hs (y_P (o_Y O)))) [] -> K2 = kdf2 (hs_ck (p_hs (y_P (o_Y O)))) [] ->
  Zlength K1 = 32 -> Zlength K2 = 32 ->
  (field_at Ews t_mk5 (DOT KC._kp) (o_kp O) k * field_at Ews t_mk5 (DOT KC._refs) (Vint (Int.repr 1)) k *
   spacer Ews 12 16 k *
   field_at Ews t_mk5 (DOT KC._held) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) k *
   field_at Ews t_mk5 (DOT KC._hashed) Vundef k * spacer Ews 25 28 k * field_at Ews t_mk5 (DOT KC._index) Vundef k *
   hbytes Ews (if hkp5_o0L_init O then K1 else K2) (field_address t_mk5 (DOT KC._send) k) *
   hbytes Ews (if hkp5_o0L_init O then K2 else K1) (field_address t_mk5 (DOT KC._recv) k) *
   field_at Ews t_mk5 (DOT KC._send_valid) (Vint Int.one) k * field_at Ews t_mk5 (DOT KC._recv_valid) (Vint Int.one) k *
   field_at Ews t_mk5 (DOT KC._initiator) (force_val (sem_cast_i2bool (Val.of_bool (hkp5_o0L_init O)))) k *
   spacer Ews 99 100 k * field_at Ews t_mk5 (DOT KC._remote_index) (Vint (hs_rindex (p_hs (y_P (o_Y O))))) k *
   field_at Ews t_mk5 (DOT KC._birth) (Vlong (y_now (o_Y O))) k *
   field_at Ews t_mk5 (DOT KC._id) Vundef k *
   field_at Ews t_mk5 (DOT KC._scnt) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) k *
   field_at Ews t_mk5 (DOT KC._rcnt) (Vlong (Int64.repr (Int.signed (Int.repr 0)))) k *
   field_at Ews t_mk5 (DOT KC._next) Vundef k)%logic
  |-- data_at Ews t_mk5 (hkp5_o0L_kv1 F O) k.
Proof.
  intros E1 E2 L1 L2.
  assert (LA1: Zlength (if hkp5_o0L_init O then K1 else K2) = 32) by (case (hkp5_o0L_init O); [exact L1 | exact L2]).
  assert (LA2: Zlength (if hkp5_o0L_init O then K2 else K1) = 32) by (case (hkp5_o0L_init O); [exact L2 | exact L1]).
  rewrite (hkp5_o0L2a_hbytes Ews _ _ LA1), (hkp5_o0L2a_hbytes Ews _ _ LA2), hkp5_o0L2a_i2bool.
  subst K1 K2.
  change (Int64.repr (Int.signed (Int.repr 0))) with Int64.zero.
  unfold hkp5_o0L_kv1, hkp5_o0L_mk, hkp5_o0_mk, o5_sn, snap_of.
  cbn [m5_kp m5_refs m5_held m5_send m5_recv m5_sv m5_rv m5_init m5_rindex m5_birth m5_scnt m5_rcnt sn_hs].
  rewrite hkp5_o0L2a_mk_eq.
  cancel.
Qed.

Lemma hkp5_o0L_2a_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R (O: hkp5_o0) :
  hkp5_model_facts -> x25519_props x25519 -> hkp5_o0L_facts F V O -> 
  semax (hkp5_Delta hkp5_G_Op0) (hkp5_o0L_1 x25519 F V steps FR i O) hkp5_o0L_s2a
    (overridePost (hkp5_o0L_1b x25519 F V steps FR i O) R).
Proof.
  intros HF HX HL.
  destruct HL as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2).
  unfold hkp5_o0L_1, hkp5_o0L_1b, hkp5_Delta.
  unfold hkp5_o0L_props, hkp5_o0_props, hkp5_o0L_locals1, hkp5_o0_locals, hkp5_o0_SEP, hkp5_o0L_SEP, hkp5_o0L_fs,
    hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbv zeta.
  cbn [app].
  set (sn := o5_sn (f_p F) O).
  set (K1 := kdf1 (hs_ck (p_hs (y_P (o_Y O)))) []).
  set (K2 := kdf2 (hs_ck (p_hs (y_P (o_Y O)))) []).
  assert (LA1: Zlength (if hkp5_o0L_init O then K1 else K2) = 32) by (case (hkp5_o0L_init O); [exact L1 | exact L2]).
  assert (LA2: Zlength (if hkp5_o0L_init O then K2 else K1) = 32) by (case (hkp5_o0L_init O); [exact L2 | exact L1]).
  Intros.
  destruct R as [Rn Rb Rc Rr].
  unfold hkp5_o0L_s2a.
  abbreviate_semax.
  sep_apply (hkp5_o0L2a_snap_open Tsh sn (f_snap F)).
  rewrite hkp5_o0L2a_mk_undef, hkp5_o0L2a_mk_eq, !hkp5_o0L2a_hout.
  repeat flatten_sepcon_in_SEP.
  freeze [1;2;3;4;5;6;7;8;9;12;13;14;15;16;17;18;19;20;21;22;23;24;25;26;27;30;32;33;34;40;43;46;47] FZ.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward.
  forward_if (temp KC._t'30 (if hkp5_o0L_init O then f_first F else f_second F)).
  { forward. entailer!. destruct (hkp5_o0L_init O); [reflexivity | match goal with Hc: typed_true _ _ |- _ => inv Hc end]. }
  { forward. entailer!. destruct (hkp5_o0L_init O); [match goal with Hc: typed_false _ _ |- _ => inv Hc end | reflexivity]. }
  sep_apply (hkp5_o0L2a_sel (hkp5_o0L_init O) Tsh K1 K2 (f_first F) (f_second F)).
  flatten_sepcon_in_SEP.
  replace (hout Ews 32 (field_address t_mk5 (DOT KC._send) (o_k O)))
    with (hout Ews (Zlength (if hkp5_o0L_init O then K1 else K2)) (field_address t_mk5 (DOT KC._send) (o_k O)))
    by (rewrite LA1; reflexivity).
  forward_call (Ews, field_address t_mk5 (DOT KC._send) (o_k O), Tsh, if hkp5_o0L_init O then f_first F else f_second F,
    if hkp5_o0L_init O then K1 else K2).
  { rewrite LA1. entailer!. simpl.
    match goal with Hf: field_compatible t_mk5 (DOT KC._kp) _ |- _ => rewrite (proj1 (hkp5_o0L2a_sr_addr _ Hf)) end.
    reflexivity. }
  forward_if (temp KC._t'31 (if hkp5_o0L_init O then f_second F else f_first F)).
  { forward. entailer!. destruct (hkp5_o0L_init O); [reflexivity | match goal with Hc: typed_true _ _ |- _ => inv Hc end]. }
  { forward. entailer!. destruct (hkp5_o0L_init O); [match goal with Hc: typed_false _ _ |- _ => inv Hc end | reflexivity]. }
  replace (hout Ews 32 (field_address t_mk5 (DOT KC._recv) (o_k O)))
    with (hout Ews (Zlength (if hkp5_o0L_init O then K2 else K1)) (field_address t_mk5 (DOT KC._recv) (o_k O)))
    by (rewrite LA2; reflexivity).
  forward_call (Ews, field_address t_mk5 (DOT KC._recv) (o_k O), Tsh, if hkp5_o0L_init O then f_second F else f_first F,
    if hkp5_o0L_init O then K2 else K1).
  { rewrite LA2. entailer!. simpl.
    match goal with Hf: field_compatible t_mk5 (DOT KC._kp) _ |- _ => rewrite (proj2 (hkp5_o0L2a_sr_addr _ Hf)) end.
    reflexivity. }
  thaw FZ.
  sep_apply (hkp5_o0L2a_unsel (hkp5_o0L_init O) Tsh K1 K2 (f_first F) (f_second F)).
  sep_apply (wand_frame_elim (field_at Tsh t_hsnap (DOT KC._remote_index) (Vint (hs_rindex (sn_hs sn))) (f_snap F))
    (@data_at HCS Tsh t_hsnap (hsnap_val sn) (f_snap F))).
  sep_apply (hkp5_o0L2a_node_fold F O (o_k O) K1 K2 eq_refl eq_refl L1 L2).
  entailer!.
Qed.
