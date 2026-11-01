(* law handshake, phase P3, segment E.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p3_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)
Local Open Scope logic.

Lemma hhs3_p3_E_hout sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hhs3_p3_E_hout32 sh bs p : Zlength bs = 32 -> hbytes sh bs p |-- hout sh 32 p.
Proof. intros <-. apply hhs3_p3_E_hout. Qed.

Lemma hhs3_p3_E_hif sh (b: bool) bs p : Zlength bs = 32 ->
  (if b then hbytes sh bs p else hout sh 32 p) |-- hout sh 32 p.
Proof. intros Hl. destruct b; [apply hhs3_p3_E_hout32; exact Hl | apply derives_refl]. Qed.

(* the harness's m_initiation: six byte buffers *)
Lemma hhs3_p3_E_minit_open sh p E encs enct ep ck h :
  @field_compatible HCS t_minit [] p ->
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 -> Zlength ep = 32 -> Zlength ck = 32 ->
  Zlength h = 32 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  hbytes sh E p * hbytes sh encs (offset_val 32 p) * hbytes sh enct (offset_val 80 p) *
  hbytes sh ep (offset_val 108 p) * hbytes sh ck (offset_val 140 p) * hbytes sh h (offset_val 172 p).
Proof.
  intros FC L1 L2 L3 L4 L5 L6.
  unfold minit_val, hbytes. rewrite L1, L2, L3, L4, L5, L6.
  unfold_data_at (@data_at HCS sh t_minit _ p).
  rewrite (@field_at_data_at HCS sh t_minit (DOT HC._ephemeral)),
    (@field_at_data_at HCS sh t_minit (DOT HC._enc_static)),
    (@field_at_data_at HCS sh t_minit (DOT HC._enc_timestamp)),
    (@field_at_data_at HCS sh t_minit (DOT HC._eph_priv)),
    (@field_at_data_at HCS sh t_minit (DOT HC._st)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (FC2: @field_compatible HCS t_mstate [] (offset_val 140 p)).
  { pose proof (@field_compatible_app HCS [] t_minit (DOT HC._st) p) as X.
    rewrite field_address_offset in X by auto with field_compatible. apply X. simpl app.
    auto with field_compatible. }
  change (Tstruct HH._m_state noattr) with t_mstate.
  unfold_data_at (@data_at HCS sh t_mstate _ (offset_val 140 p)).
  rewrite (@field_at_data_at HCS sh t_mstate (DOT HC._ck)), (@field_at_data_at HCS sh t_mstate (DOT HC._h)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !offset_offset_val. simpl Z.add. rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

(* the harness's m_identity: priv, pub as byte buffers, the flag *)
Lemma hhs3_p3_E_mident_open sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_priv I) = 32 -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  hbytes sh (mi_priv I) p * hbytes sh (mi_pub I) (offset_val 32 p) *
  @field_at HCS sh t_mident (DOT HH._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p.
Proof.
  intros FC L1 L2.
  unfold mident_val, hbytes. rewrite L1, L2.
  unfold_data_at (@data_at HCS sh t_mident _ p).
  rewrite (@field_at_data_at HCS sh t_mident (DOT HH._priv)), (@field_at_data_at HCS sh t_mident (DOT HH._pub)).
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset.
  assert (isptr p) by (destruct FC; auto).
  rewrite !(isptr_offset_val_zero p) by auto.
  apply pred_ext; cancel.
Qed.

Local Open Scope Z_scope.

Section P3E.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hhs3_p3_E_ok {Espec: OracleKind} gv L FR :
  hhs3_p3_crypto_stmt x25519 aead_enc aead_dec ->
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p3_SD x25519 aead_enc aead_dec gv L FR) hhs3_p3_E
    (overridePost (hhs3_p3_SE x25519 aead_enc aead_dec gv L FR) (hhs3_R gv)).
Proof.
  intros HC HH. unfold hhs3_p3_SD, hhs3_p3_SDE, hhs3_Delta, hhs3_R, hhs3_p3_E. simplify_func_tycontext. abbreviate_semax.
  Intros R S m1 m2 a0 f0 l0 I M1 H1. Intros MI nowb acc PA1 CI1 CI2.
  destruct MI as [[[[[E encs] enct] ep] ck] h].
  unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
  assert_PROP (Zlength E = 32 /\ Zlength encs = 48 /\ Zlength enct = 28 /\ Zlength ep = 32 /\ Zlength ck = 32 /\
               Zlength h = 32 /\ Zlength (mi_priv (hhs3_IB x25519 R)) = 32 /\ Zlength (mi_pub (hhs3_IB x25519 R)) = 32
               /\ @field_compatible HCS t_minit [] (l_mi L) /\ @field_compatible HCS t_mident [] (l_ib L)) as LMI.
  { entailer!.
    unfold minit_val in H44; simplify_value_fits in H44;
    destruct H44 as ((A1&_)&(A2&_)&(A3&_)&(A4&_)&(A5&_)&(A6&_));
    unfold bytes in A1, A2, A3, A4, A5, A6; unfold unfold_reptype in A1, A2, A3, A4, A5, A6;
    simpl in A1, A2, A3, A4, A5, A6; rewrite !Zlength_map in A1, A2, A3, A4, A5, A6.
    unfold mident_val in H41; simplify_value_fits in H41; destruct H41 as ((B1&_)&(B2&_)&_);
    unfold bytes in B1, B2; unfold unfold_reptype in B1, B2; simpl in B1, B2;
    rewrite !Zlength_map in B1, B2.
    repeat split; assumption. }
  destruct LMI as (LE & Lencs & Lenct & Lep & Lck & Lh & Lpriv & Lpub & FCmi & FCib).
  destruct HH as (Hx & Ha & _ & Hc & _).
  forward_if.
  2: { (* all_ok false *)
    forward.
    assert (OK25: hhs3_p3_ok25 x25519 R I nowb = false).
    { destruct (hhs3_p3_ok25 x25519 R I nowb); [exfalso; apply Int.one_not_zero; assumption | reflexivity]. }
    assert (OK3: hhs3_ok3 x25519 R I nowb (E, encs, enct, ep, ck, h) = false).
    { unfold hhs3_ok3. unfold hhs3_p3_ok25 in OK25. rewrite OK25. reflexivity. }
    try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal'.
    unfold hhs3_p3_SE, hhs3_p3_SDE.
    Exists R S m1 m2 a0 f0 l0 I M1 H1. Exists (E, encs, enct, ep, ck, h) nowb acc PA1 CI1 CI2.
    unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app].
    rewrite OK3, OK25. rewrite <- H4. entailer!. }
  (* all_ok true *)
  rewrite (hhs3_p3_E_minit_open Tsh (l_mi L) E encs enct ep ck h FCmi) by assumption.
  rewrite (hhs3_p3_E_mident_open Tsh (l_ib L) (hhs3_IB x25519 R) FCib) by assumption.
  forward_call (Tsh, l_d1 L, Tsh, offset_val 108 (l_mi L), ep, Tsh, offset_val 32 (l_ib L), mi_pub (hhs3_IB x25519 R)).
  { entailer!. }
  assert (OK25: hhs3_p3_ok25 x25519 R I nowb = true)
    by (destruct (hhs3_p3_ok25 x25519 R I nowb); [reflexivity | contradiction H6; reflexivity]).
  clear H6.
  set (pubB := mi_pub (hhs3_IB x25519 R)) in *.
  set (privB := mi_priv (hhs3_IB x25519 R)) in *.
  (* t'89 = dh1 && m_dh(d2, ib.priv, mi.ephemeral) *)
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    let F := eval pattern (hout Tsh 32 (l_d2 L)) in Rs in
    match F with ?G _ =>
    let Rs' := eval cbv beta in (G (if dh_ok x25519 ep pubB then hbytes Tsh (x25519 privB E) (l_d2 L)
                                    else hout Tsh 32 (l_d2 L))) in
    forward_if (PROPx P (LOCALx (temp HC._t'89 (Vint (if (dh_ok x25519 ep pubB && dh_ok x25519 privB E)%bool
                                                       then Int.one else Int.zero)) :: Q) (SEPx Rs')))
    end end.
  { destruct (dh_ok x25519 ep pubB) eqn:D1; [| contradiction].
    forward_call (Tsh, l_d2 L, Tsh, l_ib L, privB, Tsh, l_mi L, E).
    forward. entailer!. destruct (dh_ok x25519 privB E); reflexivity. }
  { destruct (dh_ok x25519 ep pubB) eqn:D1; [discriminate |].
    forward. entailer!. }
  (* t'91 = t'89 && bytes_eq(d1, d2, 32) *)
  forward_if (temp HC._t'91 (Vint (if (dh_ok x25519 ep pubB && dh_ok x25519 privB E &&
                                       bytes_eqb (x25519 ep pubB) (x25519 privB E))%bool
                                   then Int.one else Int.zero))).
  { destruct (dh_ok x25519 ep pubB) eqn:D1; [| contradiction].
    destruct (dh_ok x25519 privB E) eqn:D2; [| contradiction].
    change (if true then hbytes Tsh (x25519 privB E) (l_d2 L) else hout Tsh 32 (l_d2 L))
      with (hbytes Tsh (x25519 privB E) (l_d2 L)).
    forward_call (Tsh, l_d1 L, x25519 ep pubB, Tsh, l_d2 L, x25519 privB E).
    { rewrite Hx. entailer!. }
    { rewrite Hx; rep_lia. }
    forward. entailer!. destruct (bytes_eqb (x25519 ep pubB) (x25519 privB E)); reflexivity. }
  { forward. entailer!.
    destruct (dh_ok x25519 ep pubB), (dh_ok x25519 privB E); try reflexivity; discriminate. }
  sep_apply (hhs3_p3_E_hout32 Tsh (x25519 ep pubB) (l_d1 L) (Hx _ _)).
  sep_apply (hhs3_p3_E_hif Tsh (dh_ok x25519 ep pubB) (x25519 privB E) (l_d2 L) (Hx _ _)).
  forward.
  assert (Lssa: Zlength (hhs3_ssa x25519 R) = 32)
    by (unfold hhs3_ssa, m_precomputed_model; destruct (_ && _)%bool; [apply Hx | reflexivity]).
  assert (Lssb: Zlength (hhs3_ssb x25519 R) = 32)
    by (unfold hhs3_ssb, m_precomputed_model; destruct (_ && _)%bool; [apply Hx | reflexivity]).
  set (A1 := (dh_ok x25519 ep pubB && dh_ok x25519 privB E && bytes_eqb (x25519 ep pubB) (x25519 privB E))%bool).
  (* t'93 = agree && !bytes_zero(ssa, 32) *)
  forward_if (temp HC._t'93 (Vint (if (A1 && negb (is_zero (hhs3_ssa x25519 R)))%bool then Int.one else Int.zero))).
  { destruct A1; [| contradiction].
    forward_call (Tsh, l_ssa L, hhs3_ssa x25519 R).
    { rewrite Lssa. entailer!. }
    forward. entailer!. destruct (is_zero (hhs3_ssa x25519 R)); reflexivity. }
  { forward. entailer!. destruct A1; [discriminate | reflexivity]. }
  (* t'95 = t'93 && bytes_eq(ssa, ssb, 32) *)
  forward_if (temp HC._t'95 (Vint (if (A1 && negb (is_zero (hhs3_ssa x25519 R)) &&
                                       bytes_eqb (hhs3_ssa x25519 R) (hhs3_ssb x25519 R))%bool
                                   then Int.one else Int.zero))).
  { destruct (A1 && negb (is_zero (hhs3_ssa x25519 R)))%bool; [| contradiction].
    forward_call (Tsh, l_ssa L, hhs3_ssa x25519 R, Tsh, l_ssb L, hhs3_ssb x25519 R).
    { rewrite Lssa. entailer!. }
    forward. entailer!. destruct (bytes_eqb (hhs3_ssa x25519 R) (hhs3_ssb x25519 R)); reflexivity. }
  { forward. entailer!. destruct (A1 && negb (is_zero (hhs3_ssa x25519 R)))%bool; [discriminate | reflexivity]. }
  forward. forward.
  pose proof (HC Hc Hx Ha R L I M1 H1 (E, encs, enct, ep, ck, h) nowb H H2 H3) as [_ K].
  assert (OK3: hhs3_ok3 x25519 R I nowb (E, encs, enct, ep, ck, h) =
               (A1 && negb (is_zero (hhs3_ssa x25519 R)) && bytes_eqb (hhs3_ssa x25519 R) (hhs3_ssb x25519 R))%bool).
  { unfold hhs3_ok3. unfold hhs3_p3_ok25 in OK25. rewrite OK25. reflexivity. }
  rewrite <- OK3.
  destruct (hhs3_ok3 x25519 R I nowb (E, encs, enct, ep, ck, h)) eqn:AG.
  - assert (Hacc: acc = true) by (rewrite H4; apply K; reflexivity).
    forward_if.
    2: { exfalso; apply Int.one_not_zero; assumption. }
    match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
    + apply ENTAIL_refl.
    + forward_if.
      * rewrite Hacc in *. contradiction.
      * forward. entailer!.
    + forward. apply ENTAIL_refl.
    + try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal';
      unfold hhs3_p3_SE, hhs3_p3_SDE; subst pubB privB A1;
      Exists R S m1 m2 a0 f0 l0 I M1 H1; Exists (E, encs, enct, ep, ck, h) nowb acc PA1 CI1 CI2;
      unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app];
      rewrite (hhs3_p3_E_minit_open Tsh (l_mi L) E encs enct ep ck h FCmi) by assumption;
      rewrite (hhs3_p3_E_mident_open Tsh (l_ib L) (hhs3_IB x25519 R) FCib) by assumption;
      rewrite AG; rewrite <- H4; entailer!.
  - forward_if.
    { contradiction. }
    forward. try unfold POSTCONDITION, abbreviate; try rewrite overridePost_normal';
      unfold hhs3_p3_SE, hhs3_p3_SDE; subst pubB privB A1;
      Exists R S m1 m2 a0 f0 l0 I M1 H1; Exists (E, encs, enct, ep, ck, h) nowb acc PA1 CI1 CI2;
      unfold hhs3_p3_sep, hhs3_lvars, hhs3_globs, hhs3_setup_sep, hhs3_cnt_temps; cbn [app];
      rewrite (hhs3_p3_E_minit_open Tsh (l_mi L) E encs enct ep ck h FCmi) by assumption;
      rewrite (hhs3_p3_E_mident_open Tsh (l_ib L) (hhs3_IB x25519 R) FCib) by assumption;
      rewrite AG; rewrite <- H4; entailer!.
Qed.

End P3E.
