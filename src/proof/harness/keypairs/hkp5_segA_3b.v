(* law keypairs, prologue A, piece 3b: statements 19..20 (hnodes_snap(others); kents_snap(kes)).
   States: hkp5_segA_defs.v. "Prologue A".
*)
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
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5A_3b_pn l NS : hnodes_rep4 W_keypairs l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; cbn [hnodes_rep4].
  - entailer!.
  - Intros nx. subst l. sep_apply (@data_at_local_facts CKS). entailer!.
    match goal with X: field_compatible _ _ (hn_addr N) |- _ => destruct X as [Hp _] end.
    destruct (hn_addr N); try contradiction; simpl; auto.
Qed.

Lemma hkp5A_3b_kpn l KE : kents_rep W_keypairs l KE |-- !! is_pointer_or_null l.
Proof.
  destruct KE as [| e KE]; cbn [kents_rep].
  - entailer!.
  - Intros nx. unfold kent_cell. entailer!.
    match goal with X: field_compatible t_kent [] _ |- _ => destruct X as [Hp _] end.
    match goal with |- is_pointer_or_null ?v => destruct v; try contradiction; simpl; auto end.
Qed.

Lemma hkp5A_3b_vp (l: list val) v : Forall isptr l -> vp_ok l v -> v <> Vundef.
Proof.
  intros Hl [-> | Hv]; [discriminate|]. rewrite Forall_forall in Hl. specialize (Hl _ Hv).
  destruct v; try contradiction; discriminate.
Qed.

Lemma hkp5A_3b_snap_pre F P NS PS KE T head :
  isptr (f_w F) -> hkp5A_inv F P NS PS KE T head ->
  Forall (fun x => match x with (p, _, P) =>
            In (hs_addr p) (saddrs (t_D T)) /\ e_peer (t_entry_d T (hs_addr p)) <> Vundef /\
            hs_sid (p_hs P) <> Vundef /\
            Forall (fun v => v <> Vundef) [p_device P; p_cur P; p_prev P; p_next P; p_pknext P] end) PS.
Proof.
  intros Hw (Hp & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpa & Hka & Hq & _ & HD & _ & He & _ & _).
  rewrite Forall_forall in Hq, Hpa, He |- *. intros [[q sh] Q] Hin.
  assert (Hqa: In q (map peer_addr4 PS)) by (apply in_map_iff; exists (q, sh, Q); split; [reflexivity | exact Hin]).
  destruct (Hq _ Hin) as (Hdev & Hsid & _ & Hsl & Hpk).
  pose proof (Hpa _ Hqa) as Hqp. destruct (He _ Hqa) as [Hep _].
  rewrite Forall_forall in Hsl.
  split; [| split; [| split]].
  - rewrite HD. apply in_or_app. right. apply in_or_app. left. apply in_map, Hqa.
  - rewrite Hep. destruct q; try contradiction; discriminate.
  - rewrite Hsid. unfold id_addr. destruct (f_w F); try contradiction; discriminate.
  - repeat constructor.
    + rewrite Hdev. destruct (f_w F); try contradiction; discriminate.
    + apply (hkp5A_3b_vp _ _ Hka), Hsl; cbn; auto.
    + apply (hkp5A_3b_vp _ _ Hka), Hsl; cbn; auto.
    + apply (hkp5A_3b_vp _ _ Hka), Hsl; cbn; auto.
    + apply (hkp5A_3b_vp (f_p F :: map peer_addr4 PS)); [constructor; [exact Hp | rewrite Forall_forall; exact Hpa] | exact Hpk].
Qed.

Lemma hkp5A_3b_ksnap_pre F P NS PS KE T head :
  hkp5A_inv F P NS PS KE T head ->
  Forall (fun e => In (ke_addr e) (saddrs (t_D T)) /\ e_peer (t_entry_d T (ke_addr e)) <> Vundef) KE.
Proof.
  intros (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpa & _ & _ & _ & HD & _ & _ & Hk & _).
  rewrite Forall_forall in Hk, Hpa |- *. intros e He. split.
  - rewrite HD. apply in_or_app. left. apply in_map, He.
  - specialize (Hk _ He). specialize (Hpa _ Hk). destruct (e_peer _); try contradiction; discriminate.
Qed.

Lemma hkp5A_3b_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5A_SK x25519 F FR) hkp5A_s3b (overridePost (hkp5A_S3 x25519 F FR) R).
Proof.
  intros Hx. unfold hkp5A_SK, hkp5A_s3b, hkp5_Delta. simplify_func_tycontext. abbreviate_semax.
  Intros R0 P S w NS PS KE T head.
  unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
  assert_PROP (isptr (f_w F) /\ isptr (f_t F)) as Hlv by entailer!. destruct Hlv as [Hw Ht].
  assert_PROP (is_pointer_or_null (hkp5A_nhead NS)) as Hpn by (sep_apply (hkp5A_3b_pn (hkp5A_nhead NS) NS); entailer!).
  assert_PROP (is_pointer_or_null (hkp5A_khead KE)) as Hkn by (sep_apply (hkp5A_3b_kpn (hkp5A_khead KE) KE); entailer!).
  forward.
  forward_call (hkp5A_nhead NS, NS, PS, Tsh, f_t F, T).
  { pose proof (hkp5A_3b_snap_pre F P NS PS KE T head Hw H1) as Hs.
    destruct H1 as (_ & _ & _ & _ & _ & _ & _ & Hnp & Hwf & _). repeat split; auto. }
  forward.
  forward_call (hkp5A_khead KE, KE, Tsh, f_t F, T).
  { apply (hkp5A_3b_ksnap_pre F P NS PS KE T head H1). }
  destruct R. cbv match.
  unfold hkp5A_S3. Exists R0 P S w NS PS KE T head.
  unfold hkp5A_world, hkp5A_snaps0, hkp5A_oth, hkp5A_kes, hkp5A_globs, hkp5A_temps, hkp5_lvars, hk5_items; cbn [app].
  entailer!.
Qed.
