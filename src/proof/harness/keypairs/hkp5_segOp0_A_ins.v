(* law keypairs, segment Op0 part A: the pure fact of piece A2:
   wg_index_hashtable_insert of the handshake's entry with a fresh index keeps hk5_rel.
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
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_defs.
Require Import WgNoise.proof.harness.keypairs.hkp5_segOp0_A_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_o0Ains_sfind_other {A: Type} (D: list (val * share * A)) a b v :
  b <> a -> sfind (supd D a v) b = sfind D b.
Proof.
  intros Hne. induction D as [|[[x sh] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; destruct (EqDec_val x b); subst; try congruence; auto.
Qed.

Lemma hkp5_o0Ains_sfind_same {A: Type} (D: list (val * share * A)) a sh v w :
  sfind D a = Some (sh, w) -> sfind (supd D a v) a = Some (sh, v).
Proof.
  induction D as [|[[x sh'] w'] D IH]; simpl; [discriminate|].
  destruct (EqDec_val x a); subst; simpl.
  - intros Hs; inversion Hs; subst. destruct (EqDec_val a a); [auto|congruence].
  - intros Hs. destruct (EqDec_val x a); [congruence|]. auto.
Qed.

Lemma hkp5_o0Ains_saddrs {A: Type} (D: list (val * share * A)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [|[[x sh] w] D IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; auto. unfold saddrs in IH |- *. simpl. f_equal. exact IH.
Qed.

Lemma hkp5_o0Ains_vremove_notin a L : ~ In a (vremove a L).
Proof.
  induction L as [|x L IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; auto. intros [Hx|Hx]; [congruence|auto].
Qed.

Lemma hkp5_o0Ains_vremove_in a L b : b <> a -> (In b (vremove a L) <-> In b L).
Proof.
  intros Hne. induction L as [|x L IH]; simpl; [tauto|].
  destruct (EqDec_val x a); subst; simpl; [|rewrite IH]; split; intros; try tauto.
  destruct H as [H|H]; [congruence|tauto].
Qed.

Lemma hkp5_o0Ains_vin a L b : b <> a -> vin b (a :: vremove a L) = vin b L.
Proof.
  intros Hne. unfold vin.
  destruct (in_dec eq_dec b (a :: vremove a L)) as [H1|H1];
  destruct (in_dec eq_dec b L) as [H2|H2]; auto; exfalso.
  - destruct H1 as [H1|H1]; [congruence|]. apply H2. apply (hkp5_o0Ains_vremove_in a L b Hne). auto.
  - apply H1. right. apply (hkp5_o0Ains_vremove_in a L b Hne). auto.
Qed.

Lemma hkp5_o0Ains_nodup_map {B: Type} (f: val -> B) a L : NoDup (map f L) -> NoDup (map f (vremove a L)).
Proof.
  induction L as [|x L IH]; simpl; auto.
  intros Hn. inversion Hn; subst.
  destruct (EqDec_val x a); simpl; auto.
  constructor; auto.
  intros Hin. apply H1. apply in_map_iff in Hin. destruct Hin as [y [Hy Hin]].
  apply in_map_iff. exists y. split; auto.
  destruct (EqDec_val y a) as [->|Hya]; [exfalso; exact (hkp5_o0Ains_vremove_notin a L Hin)|].
  apply (hkp5_o0Ains_vremove_in a L y Hya). auto.
Qed.

Lemma hkp5_o0Ains_indices D a v L1 L2 L :
  ~ In a L -> t_indices (mkT (supd D a v) L1) L = t_indices (mkT D L2) L.
Proof.
  intros Hn. unfold t_indices, t_entry. simpl. apply map_ext_in. intros b Hb.
  rewrite hkp5_o0Ains_sfind_other; auto. intros ->. auto.
Qed.

Lemma hkp5_o0A_ins_ok : hkp5_o0A_ins_fact.
Proof.
  intros p OD OH H P KS T idx HR Hfr Hwf.
  destruct HR as [HC HR'].
  split; [|exact HR'].
  destruct HC as (HF & H1 & H2 & H3 & H4 & H5 & H6 & H7 & HP).
  destruct HP as (HD & HnKS & HnOD & HKO & [idx0 Hs] & HOD & HN & _).
  assert (Ht: t_insert T (hs_addr p) idx =
    mkT (supd (t_D T) (hs_addr p) (mkEntry p IDX_HANDSHAKE idx)) (hs_addr p :: vremove (hs_addr p) (t_L T))).
  { unfold t_insert, t_set_index, t_upd, t_entry. rewrite Hs. reflexivity. }
  rewrite Ht in Hwf |- *.
  refine (conj _ (conj H1 (conj H2 (conj H3 (conj H4 (conj H5 (conj H6 (conj H7 _)))))))).
  - clear -HF HnKS. induction HF as [|x y ML KS' [Hxy HM] HF IH]; constructor.
    + split; auto. simpl in HnKS.
      assert (Hne: m5_kp (snd x) <> hs_addr p). { rewrite <- Hxy. intros He. apply HnKS. left. auto. }
      destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10).
      repeat split; auto; simpl.
      * rewrite hkp5_o0Ains_sfind_other; auto.
      * rewrite hkp5_o0Ains_vin; auto.
    + apply IH. simpl in HnKS. tauto.
  - refine (conj _ (conj HnKS (conj HnOD (conj HKO (conj _ (conj _ (conj _ Hwf))))))).
    + intros b. simpl. rewrite hkp5_o0Ains_saddrs. apply HD.
    + exists idx. simpl. eapply hkp5_o0Ains_sfind_same. exact Hs.
    + clear -HOD HnOD. induction OD as [|[[a sh] E] OD IH]; constructor.
      * inversion HOD; subst. destruct H1 as [Hf Hv].
        assert (Hne: a <> hs_addr p). { intros ->. apply HnOD. left. reflexivity. }
        simpl. rewrite hkp5_o0Ains_sfind_other by auto. rewrite hkp5_o0Ains_vin by auto. auto.
      * inversion HOD; subst. apply IH; auto. intros Hin. apply HnOD. right. exact Hin.
    + unfold t_indices at 1. simpl. unfold t_entry at 1. simpl.
      rewrite (hkp5_o0Ains_sfind_same _ _ _ _ _ Hs).
      fold (t_indices (mkT (supd (t_D T) (hs_addr p) (mkEntry p IDX_HANDSHAKE idx))
                           (hs_addr p :: vremove (hs_addr p) (t_L T))) (vremove (hs_addr p) (t_L T))).
      rewrite (hkp5_o0Ains_indices _ _ _ _ (t_L T)) by apply hkp5_o0Ains_vremove_notin.
      simpl. constructor.
      * exact Hfr.
      * destruct T as [D L]. apply hkp5_o0Ains_nodup_map. exact HN.
Qed.
