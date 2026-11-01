(* law handshake_receive, B8 R B part C3: the pure facts the CHECK of C3
   needs about the accepted peer (index j of PS), its node and its handshake entry. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.

Local Open Scope Z_scope.

Lemma hrx5_B8RBC3_sfind : forall (PS: list (val * share * peer)) a sh P, NoDup (map peer_addr4 PS) ->
  In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8RBC3_sfind_in {A: Type} : forall (l: list (val * share * A)) x r, sfind l x = Some r ->
  In x (saddrs l).
Proof.
  induction l as [|[[y sh] v] l IH]; simpl; intros x r H; [discriminate|].
  destruct (EqDec_val y x) as [<-|n]; [left; reflexivity | right; exact (IH _ _ H)].
Qed.

Lemma hrx5_B8RBC3_F2_sh {A: Type} (Rl: A -> val * share * entry -> Prop) (l1: list A) (l2: list (val * share * entry)) :
  (forall k x, Rl k x -> match x with (_, sh, _) => sh = Ews end) ->
  Forall2 Rl l1 l2 -> Forall (fun d => match d with (_, sh, _) => sh = Ews end) l2.
Proof.
  intros HR H; induction H as [|k x l1 l2 Hkx HF IH]; constructor; [exact (HR _ _ Hkx) | exact IH].
Qed.

Lemma hrx5_B8RBC3_pool_sh: forall KA PS T, hrx5cr_pool KA PS T ->
  Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T).
Proof.
  intros KA PS T (H1 & H2). rewrite <- (firstn_skipn (length KA) (t_D T)). apply Forall_app. split.
  - eapply hrx5_B8RBC3_F2_sh; [| exact H1]. intros k [[a sh] E] (_ & Hs & _). exact Hs.
  - eapply hrx5_B8RBC3_F2_sh; [| exact H2]. intros [[p s] P] [[a sh] E] (_ & Hs & _). exact Hs.
Qed.

Lemma hrx5_B8RBC3_snapped_len T NS PS : Zlength NS = Zlength PS ->
  Zlength (hnodes_snapped4 T NS PS) = Zlength PS.
Proof.
  intros H. unfold hnodes_snapped4. rewrite Zlength_map.
  rewrite !Zlength_correct in *. rewrite combine_length. lia.
Qed.

Section Facts.
Variable x25519: list byte -> list byte -> list byte.

Lemma hrx5_B8RBC3_facts R L NS PS KE T head nk a P j r :
  hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= j < Zlength PS -> Znth j PS = (a, Ews, P) ->
  Zlength NS = Zlength PS -> sfind (t_D T) (hs_addr a) = Some r ->
  sfind PS a = Some (Ews, P) /\ hs_ok (p_hs P) /\ hs_sid (p_hs P) = id_addr (l_wd L) /\
  In (hs_addr a) (saddrs (t_D T)) /\ Forall (fun d => match d with (_, sh, _) => sh = Ews end) (t_D T) /\
  In (Znth j (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS).
Proof.
  intros Hinv Hj HZ HL Hs.
  destruct Hinv as (Hpok & _ & Hnd & _ & _ & _ & Hpool).
  assert (Hin: In (a, Ews, P) PS) by (rewrite <- HZ; apply Znth_In; exact Hj).
  pose proof (proj1 (Forall_forall _ _) Hpok _ Hin) as Hok.
  destruct Hok as (_ & _ & Hsid & Hhs & _).
  split; [apply hrx5_B8RBC3_sfind; auto|].
  split; [exact Hhs|]. split; [exact Hsid|].
  split; [exact (hrx5_B8RBC3_sfind_in _ _ _ Hs)|].
  split; [exact (hrx5_B8RBC3_pool_sh _ _ _ Hpool)|].
  apply Znth_In. rewrite hrx5_B8RBC3_snapped_len by auto. exact Hj.
Qed.

End Facts.
