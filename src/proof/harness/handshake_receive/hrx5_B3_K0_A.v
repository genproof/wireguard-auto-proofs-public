(* law handshake_receive, phase B3, branch kind 0, segment A:
   stmts 0..5: len = draw_size(); bump off 148/92/64; len > 0xffffffff -> continue (hrx5_SC); buf = malloc(len) (malloc_spec' at tarray tuchar len); NULL -> continue; nondet_bytes(buf, len).
   States and statements: hrx5_B3_K0_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B3_K0_defs.
Local Open Scope logic.

Lemma k0a_eq64 n m : 0 <= n <= Int64.max_unsigned -> 0 <= m <= Int64.max_unsigned ->
  Int64.eq (Int64.repr n) (Int64.repr m) = (n =? m).
Proof.
  intros Hn Hm. unfold Int64.eq. rewrite !Int64.unsigned_repr by lia.
  destruct (zeq n m), (Z.eqb_spec n m); congruence.
Qed.

(* byte arrays are the same in every compspecs (port of hrx5_k_lib's hrx5_k_tuchar_cs) *)
Lemma k0a_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma k0a_fc_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (k0a_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (k0a_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma k0a_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply k0a_fc_tuchar_cs.
Qed.

Lemma k0a_map_bytes (bs: list Z) :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  map (fun b => Vint (Int.repr b)) bs = bytes (map Byte.repr bs).
Proof.
  induction 1 as [|b bs Hb _ IH]; [reflexivity|].
  unfold bytes in *. simpl. rewrite IH. f_equal. unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia.
  reflexivity.
Qed.

Lemma k0a_bytes_at sh (bs: list Z) p :
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W sh (tarray tuchar (Zlength bs)) (map (fun b => Vint (Int.repr b)) bs) p |--
  bytes_at sh (map Byte.repr bs) p.
Proof.
  intros HF. unfold bytes_at. rewrite Zlength_map, (k0a_map_bytes bs HF).
  rewrite (@k0a_tuchar_cs W Noise.CS). apply derives_refl.
Qed.

Ltac k0a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1 :=
  unfold hrx5_SC, hrx5_SLc;
  Exists R sec birth S w NS PS T head; Exists nk KE st i kc lul;
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, hrx5_rglobs, hrx5_skb0; cbn [app];
  unfold hrx5_skb_part, qlen_rep; Intros dv lv;
  go_lower;
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 _))); repeat split; auto; try lia;
     try (rewrite eqb_type_refl; reflexivity) |];
  sep_apply (@data_at_data_at_ HRX Ews tint);
  sep_apply (@data_at_data_at_ Cookie.CS Tsh t_skb);
  cancel.

Section K0A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_K0_A_ok {Espec: OracleKind} gv L FR :
  hrx5_B3_lem_stmt x25519 ->
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_B3_P x25519 0 gv L FR) hrx5_K0_A
    (overridePost (hrx5_K0_M x25519 gv L FR) (hrx5_RB x25519 gv L FR)).
Proof.
  intros HLEM HY. unfold hrx5_Delta, hrx5_B3_P.
  Intros R sec birth S w NS PS T head. Intros nk KE st i kc lul q proto. Intros ip4 ip6 port.
  unfold hrx5_K0_A, hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr; cbn [app].
  unfold hrx5_RB, hrx5_R.
  abbreviate_semax.
  forward_call tt. Intros n.
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'32 (Vint (if orb (n =? 148) (n =? 92) then Int.one else Int.zero)) :: Q)
      (SEPx R))) end.
  { forward. entailer!.
    match goal with Hx: Int64.eq _ _ = true |- _ => rewrite k0a_eq64 in Hx by rep_lia; rewrite Hx end. reflexivity. }
  { forward. entailer!.
    match goal with Hx: Int64.repr n <> Int64.repr 148 |- _ =>
      assert (n =? 148 = false) as -> by (apply Z.eqb_neq; intro; subst; auto) end.
    unfold Int64.cmpu; rewrite k0a_eq64 by rep_lia. simpl. destruct (n =? 92); reflexivity. }
  match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HRM._t'33
      (Vint (if orb (orb (n =? 148) (n =? 92)) (n =? 64) then Int.one else Int.zero)) :: Q) (SEPx R))) end.
  { forward. entailer!.
    match goal with Hx: _ <> Int.zero |- _ => revert Hx end.
    destruct (orb (n =? 148) (n =? 92)); intros Hx; [reflexivity|]. exfalso; apply Hx; reflexivity. }
  { forward. entailer!.
    match goal with Hx: _ = Int.zero |- _ => revert Hx end.
    destruct (orb (n =? 148) (n =? 92)); intros Hx; [discriminate|].
    unfold Int64.cmpu; rewrite k0a_eq64 by rep_lia. simpl. destruct (n =? 64); reflexivity. }
  set (b := orb (orb (n =? 148) (n =? 92)) (n =? 64)).
  set (n1 := if b then n + 1 else n).
  assert (Hn1: 0 <= n1 <= Int64.max_unsigned /\ n1 <> 148 /\ n1 <> 92 /\ n1 <> 64).
  { subst n1 b. destruct (n =? 148) eqn:E1; [apply Z.eqb_eq in E1; subst; simpl; rep_lia|].
    destruct (n =? 92) eqn:E2; [apply Z.eqb_eq in E2; subst; simpl; rep_lia|].
    destruct (n =? 64) eqn:E3; [apply Z.eqb_eq in E3; subst; simpl; rep_lia|].
    simpl. apply Z.eqb_neq in E1, E2, E3. lia. }
  match goal with |- semax _ (PROPx ?P (LOCALx (?a :: ?b :: _ :: ?Q) (SEPx ?R))) _ _ =>
    forward_if (PROPx P (LOCALx (a :: b :: temp HRM._len (Vlong (Int64.repr n1)) :: Q) (SEPx R))) end.
  { forward. entailer!. unfold n1.
    match goal with Hx: _ <> Int.zero |- _ => revert Hx end.
    destruct b; intros Hx; [reflexivity|]. exfalso; apply Hx; reflexivity. }
  { forward. entailer!. unfold n1.
    match goal with Hx: _ = Int.zero |- _ => revert Hx end.
    destruct b; intros Hx; [discriminate|reflexivity]. }
  clearbody n1.
  destruct (Z_le_gt_dec n1 Int.max_unsigned) as [Hle|Hgt].
  2: { forward_if.
       - forward. k0a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1.
       - exfalso. match goal with Hx: Int.unsigned (Int.repr (-1)) >= n1 |- _ =>
           change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned in Hx end. lia. }
  forward_if.
  { exfalso. match goal with Hx: Int.unsigned (Int.repr (-1)) < n1 |- _ =>
      change (Int.unsigned (Int.repr (-1))) with Int.max_unsigned in Hx end. lia. }
  forward_call (tarray tuchar n1, gv).
  { simpl. rep_lia. }
  Intros buf.
  destruct (eq_dec buf nullval) as [Hb|Hb].
  { forward_if.
    - forward. k0a_sc R sec birth S w NS PS T head nk KE st i kc lul H H0 H1.
    - subst buf. exfalso. auto. }
  Intros.
  forward_if.
  { contradiction. }
  assert_PROP (malloc_compatible n1 buf) as Hmc.
  { go_lower. sep_apply (malloc_token_local_facts Ews (tarray tuchar n1) buf). Intros. apply prop_right.
    simpl in *. rewrite ?Z.max_r in * by lia. rewrite Z.mul_1_l in *. assumption. }
  forward_call (buf, n1, Ews).
  Intros bs.
  match goal with Hz: Zlength bs = n1 |- _ => subst n1 end.
  sep_apply (k0a_bytes_at Ews bs buf ltac:(assumption)).
  unfold hrx5_K0_M, hrx5_K0_Mc.
  Exists R sec birth S w NS PS T head. Exists nk KE st i kc lul q proto.
  Exists ip4 ip6 port (map Byte.repr bs) buf.
  unfold hrx5_ltemps, hrx5_lvars, hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_scr, obj_rep; cbn [app].
  rewrite Zlength_map.
  go_lower.
  apply andp_right;
    [apply prop_right; refine (conj H (conj H0 (conj H1 (conj H2 _)))); simpl obj_ok; rewrite ?Zlength_map;
     repeat split; auto; try lia; try (rewrite eqb_type_refl; reflexivity) |].
  cancel.
Qed.

End K0A.
