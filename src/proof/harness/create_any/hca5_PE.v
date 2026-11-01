(* law create_any: Segment E = statements 21..24 (hs_take(&s, &p.handshake); hs_take(&x, &p.handshake); op = nondet_u8() & 1; ok = 0), from hca5_SK to hca5_SE.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

Lemma hca5_PE_sfind (p: val) (KD: list kdraw) (E: entry) :
  ~ In (hs_addr p) (map kd_addr KD) ->
  sfind (map (hca5_kpool p) KD ++ [(hs_addr p, Tsh, E)]) (hs_addr p) = Some (Tsh, E).
Proof.
  induction KD as [|K KD IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_PE_entry_peer (p: val) (KD: list kdraw) (T: tstate) :
  hca5_pool p KD T -> exists E, t_entry T (hs_addr p) = Some E /\ e_peer E = p.
Proof.
  intros [[E [HD [HP _]]] [Hnd _]]. exists E. split; [| exact HP]. unfold t_entry. rewrite HD.
  inversion Hnd; subst. rewrite hca5_PE_sfind by assumption. reflexivity.
Qed.

Lemma hca5_PE_in (p: val) (KD: list kdraw) (T: tstate) :
  hca5_pool p KD T -> In (hs_addr p) (saddrs (t_D T)).
Proof.
  intros [[E [HD _]] _]. rewrite HD. unfold saddrs. rewrite map_app. apply in_or_app. right. simpl. auto.
Qed.

(* op = nondet_u8() & 1 *)
Lemma hca5_PE_and1 u : (0 <= u <= Byte.max_unsigned)%Z ->
  Int.and (Int.repr u) (Int.repr 1) = Int.repr (u mod 2).
Proof.
  intros Hu.
  change (Int.repr 1) with (Int.repr (two_p 1 - 1)). rewrite <- Int.zero_ext_and by lia.
  rewrite <- (Int.repr_unsigned (Int.zero_ext _ _)). rewrite Int.zero_ext_mod by (cbv; intuition congruence).
  rewrite Int.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hca5_PE_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SK x25519 gv L FR w)
    hca5_PE
    (overridePost (hca5_SE x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SK, hca5_Delta, hca5_R, hca5_PE. simplify_func_tycontext. abbreviate_semax.
  Intros R S P T KD.
  destruct (hca5_PE_entry_peer (l_p L) KD T H1) as [E [HE HEp]].
  pose proof (hca5_PE_in (l_p L) KD T H1) as HIn.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  assert_PROP (isptr (l_p L) /\ isptr (l_wa L)) as HPP by entailer!. destruct HPP as [Pp Pwa].
  assert (e_peer (t_entry_d T (hs_addr (l_p L))) <> Vundef)
    by (unfold t_entry_d; rewrite HE, HEp; destruct (l_p L); simpl in Pp; congruence).
  assert (hs_sid (p_hs P) <> Vundef)
    by (destruct H0 as (_ & Hsid & _); rewrite Hsid; unfold id_addr; destruct (l_wa L); simpl in Pwa; try contradiction; discriminate).
  assert (Hsn: hs_snap_cur T (l_p L) P = snap_of T (hs_addr (l_p L)) E (p_hs P))
    by (unfold hs_snap_cur, t_entry_d; rewrite HE; reflexivity).
  change (peer_rep Tsh (l_p L) P) with (hs_mem true Tsh (l_p L) P).
  forward_call (Tsh, l_s L, Tsh, l_p L, P, true, Tsh, l_ita L, T).
  forward_call (Tsh, l_x L, Tsh, l_p L, P, true, Tsh, l_ita L, T).
  forward_call tt. Intros u.
  forward.
  forward.
  rewrite (hca5_PE_and1 u) by assumption.
  pose proof (Z.mod_pos_bound u 2 ltac:(lia)).
  unfold hca5_SE. apply exp_right with (u mod 2). apply andp_right. { apply prop_right; lia. }
  unfold hca5_SEo. Exists R S P T KD E.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite Hsn. unfold hs_mem.
  entailer!.
Qed.
