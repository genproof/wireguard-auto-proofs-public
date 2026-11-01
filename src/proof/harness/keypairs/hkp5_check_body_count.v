(* law keypairs: pure: count_index and the table's length.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
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
Require Import WgNoise.proof.harness.keypairs.hkp5_check_body_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope Z_scope.

Lemma hkc5_count_vin_iff a L : vin a L = true <-> In a L.
Proof. unfold vin. destruct (in_dec _ a L); split; intros; auto; try discriminate; contradiction. Qed.

(* a duplicate-free list of elements of a duplicate-free U is as long as U filtered by membership in it *)
Lemma hkc5_count_len_filter (L U: list val) :
  NoDup L -> NoDup U -> incl L U -> length L = length (filter (fun a => vin a L) U).
Proof.
  intros HL HU Hi. apply Permutation_length. apply NoDup_Permutation; auto.
  - apply NoDup_filter; auto.
  - intros x. rewrite filter_In, hkc5_count_vin_iff. split; [intros Hx; split; auto | tauto].
Qed.

Lemma hkc5_count_forall2_len p T (ML: list (val * hk5_mk)) (KS: list (val * keypair)) :
  Forall2 (fun x y => fst y = m5_kp (snd x) /\ hk5_match p T (snd x) (snd y)) ML KS ->
  length (filter (fun a => vin a (t_L T)) (map fst KS)) = length (filter (fun x => m5_hashed (snd x)) ML).
Proof.
  intros HF. induction HF as [|x y ML KS [Hf Hm] HF IH]; simpl; auto.
  destruct Hm as (_ & _ & Hv & _). rewrite Hf, Hv. destruct (m5_hashed (snd x)); simpl; auto.
Qed.

Lemma hkc5_count_filter_map {A B: Type} (f: B -> bool) (g: A -> B) (l: list A) :
  length (filter f (map g l)) = length (filter (fun x => f (g x)) l).
Proof. induction l as [|x l IH]; simpl; auto. destruct (f (g x)); simpl; auto. Qed.

Lemma hkc5_count_filter_nil (i: int) (l: list int) :
  ~ In i l -> filter (fun j => Int.eq j i) l = [].
Proof.
  induction l as [|y l IH]; simpl; intros Hn; auto.
  pose proof (Int.eq_spec y i) as E. destruct (Int.eq y i); [exfalso; apply Hn; auto|].
  apply IH. tauto.
Qed.

Lemma hkc5_count_index : hkc5_count_index_stmt.
Proof.
  intros T a E HN Ha HE. unfold count_index.
  assert (Hin: In (e_index E) (t_indices T (t_L T))).
  { unfold t_indices. apply in_map_iff. exists a. rewrite HE. auto. }
  revert HN Hin. generalize (t_indices T (t_L T)) as l. intros l HN Hin.
  induction HN as [|x l Hx HN IH]; [contradiction|].
  simpl. pose proof (Int.eq_spec x (e_index E)) as Ex. destruct (Int.eq x (e_index E)).
  - subst x. rewrite hkc5_count_filter_nil by auto. reflexivity.
  - apply IH. destruct Hin as [Hin|Hin]; [congruence|auto].
Qed.

Lemma hkc5_count_table_len : hkc5_table_len_stmt.
Proof.
  intros F V Y O HI HO HND.
  destruct HI as (HR & _).
  destruct HR as (HC & _).
  destruct HC as (HF & _ & _ & HNK & _ & _ & _ & _ & HP).
  destruct HP as (HD & HpK & HpO & HKO & _ & _ & _ & HW).
  destruct HW as (HNL & HiL & _ & _).
  destruct HO as (_ & _ & _ & _ & _ & _ & HOD & _).
  set (L := t_L (y_T Y)) in *.
  set (pa := map peer_addr4 (o_PS O)) in *.
  set (ka := map ke_addr (o_KE O)) in *.
  assert (HOD': forall a, In a (saddrs (v_OD V)) <-> In a (map hs_addr pa ++ ka)).
  { intros a. rewrite HOD, in_app_iff. tauto. }
  assert (HU: NoDup (hs_addr (f_p F) :: map fst (y_KS Y) ++ (map hs_addr pa ++ ka))).
  { constructor.
    - rewrite in_app_iff. intros [H|H]; [tauto|]. apply HpO, HOD'; auto.
    - apply List.NoDup_app; auto.
      intros a Ha1 Ha2. apply (HKO a Ha1), HOD'; auto. }
  assert (Hi: incl L (hs_addr (f_p F) :: map fst (y_KS Y) ++ (map hs_addr pa ++ ka))).
  { intros a Ha. apply HiL, HD in Ha.
    destruct Ha as [<-|[Ha|Ha]]; [left; auto|right; apply in_app_iff; auto|].
    right; apply in_app_iff; right; apply HOD'; auto. }
  pose proof (hkc5_count_len_filter _ _ HNL HU Hi) as Hlen.
  pose proof (hkc5_count_forall2_len _ _ _ _ HF) as Hlen2.
  change (hs_addr (f_p F) :: ?l) with ([hs_addr (f_p F)] ++ l) in Hlen.
  rewrite !filter_app, !app_length in Hlen.
  fold L in Hlen2. rewrite Hlen2 in Hlen. unfold pa, ka in Hlen. rewrite map_map, !hkc5_count_filter_map in Hlen.
  unfold hkc5_nh, hkc5_oh, kents_hashed_n. rewrite !Zlength_correct.
  fold L. rewrite Hlen.
  cbn [filter]. destruct (vin (hs_addr (f_p F)) L); cbn [length]; lia.
Qed.

Lemma hkc5_count_ok : hkc5_count_index_stmt /\ hkc5_table_len_stmt.
Proof.
  split; [apply hkc5_count_index | apply hkc5_count_table_len].
Qed.
