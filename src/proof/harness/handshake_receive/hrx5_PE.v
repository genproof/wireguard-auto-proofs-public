(* law handshake_receive: main's phase PE = the kents and steps (statements 18..19).
   From hrx5_SB to hrx5_SE (hrx5_defs.v; the cut: hrx5_cut.v). *)
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
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* pure lemmas (port of hcr5_pk_lemmas.v): the table after kents_add        *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_pe_te (d: kdraw) : val * share * entry :=
  (kd_addr d, Ews, mkEntry (kd_owner d) IDX_KEYPAIR (kd_idx d)).

Lemma hrx5_pe_tD_kents T KD : t_D (kents_T T KD) = map hrx5_pe_te KD ++ t_D T.
Proof.
  induction KD as [| d KD IH]; cbn [kents_T map app]; auto.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd. simpl.
  destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence]. simpl.
  destruct (EqDec_val (kd_addr d) (kd_addr d)); [| congruence]. simpl.
  rewrite IH. reflexivity.
Qed.

Lemma hrx5_pe_firstn {A: Type} (l1 l2: list A) : firstn (length l1) (l1 ++ l2) = l1.
Proof. induction l1; simpl; f_equal; auto. Qed.

Lemma hrx5_pe_skipn {A: Type} (l1 l2: list A) : skipn (length l1) (l1 ++ l2) = l2.
Proof. induction l1; simpl; auto. Qed.

Lemma hrx5_pe_paddr_addr4 PS : map hrx5cr_paddr PS = map peer_addr4 PS.
Proof. apply map_ext. intros [[? ?] ?]. reflexivity. Qed.

Lemma hrx5_pe_ke_F2 PS KD :
  Forall (fun d => In (kd_owner d) (map hrx5cr_paddr PS)) KD ->
  Forall2 (hrx5cr_ke_ok PS) (map kd_addr KD) (map hrx5_pe_te KD).
Proof.
  induction 1 as [| d KD Hd H IH]; simpl; constructor; auto.
  unfold hrx5cr_ke_ok, hrx5_pe_te; simpl. auto.
Qed.

Lemma hrx5_pe_kaddr KD : map ke_addr (map kd_kent KD) = map kd_addr KD.
Proof. rewrite map_map. reflexivity. Qed.

Lemma hrx5_pe_khead KD : hrx5_khead (map kd_kent KD) = kents_head KD.
Proof. destruct KD; reflexivity. Qed.

Lemma hrx5_pe_pool PS T KD :
  hrx5cr_pool [] PS T -> kents_draws_ok PS KD ->
  hrx5cr_pool (map ke_addr (map kd_kent KD)) PS (kents_T T KD).
Proof.
  intros [_ Hhs] [HKD _]. simpl in Hhs.
  unfold hrx5cr_pool. rewrite hrx5_pe_kaddr, hrx5_pe_tD_kents, map_length.
  rewrite <- (map_length hrx5_pe_te KD), hrx5_pe_firstn, hrx5_pe_skipn. split; [| exact Hhs].
  apply hrx5_pe_ke_F2. rewrite hrx5_pe_paddr_addr4.
  eapply Forall_impl; [| exact HKD]. simpl; tauto.
Qed.

Lemma hrx5_pe_kents_PS0 PS KD : kents_PS false PS KD = PS.
Proof. induction KD; simpl; auto. Qed.

Lemma hrx5_pe_inv x25519 R L NS PS T head nk KD :
  hrx5_inv x25519 R L NS PS [] T head nk -> kents_draws_ok PS KD ->
  hrx5_inv x25519 R L NS PS (map kd_kent KD) (kents_T T KD) head nk.
Proof.
  intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) HKD.
  repeat (split; [assumption |]). apply hrx5_pe_pool; auto.
Qed.

(* kents_add's precondition *)
Lemma hrx5_pe_owners NS PS :
  hnodes_peers4 NS PS -> (NS <> [] -> hrx5_head NS <> nullval) ->
  kents_owners_ok (hrx5_head NS) nullval NS PS.
Proof.
  intros Hnp Hh. unfold kents_owners_ok. destruct NS as [| N NS].
  - unfold hnodes_peers4 in Hnp. simpl in Hnp |- *. split; auto.
  - simpl hrx5_head in *. rewrite if_false by (apply Hh; discriminate). split; [discriminate | auto].
Qed.

Lemma hrx5_pe_head_ptr NS :
  hnodes_rep4 W (hrx5_head NS) NS |--
  !! (is_pointer_or_null (hrx5_head NS) /\ (NS <> [] -> hrx5_head NS <> nullval)).
Proof.
  destruct NS as [| N NS]; simpl.
  - apply prop_right. split; [reflexivity | congruence].
  - Intros nx. entailer!.
    match goal with H: field_compatible _ _ (hn_addr N) |- _ => destruct H as [Hp _] end.
    split; [apply isptr_is_pointer_or_null; auto |].
    intros _ E. rewrite E in Hp. inv Hp.
Qed.

Section PE.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_PE_ok {Espec: OracleKind} gv L FR :
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec) (hrx5_SB x25519 gv L FR) hrx5_PE
    (overridePost (hrx5_SE x25519 gv L FR) (hrx5_R gv)).
Proof.
  intros HH. unfold hrx5_SB, hrx5_Delta, hrx5_R, hrx5_PE. simplify_func_tycontext.
  Intros R sec birth S w. Intros NS PS T head nk.
  abbreviate_semax.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_lvars, hrx5_scr; cbn [app].
  assert_PROP (is_pointer_or_null (hrx5_head NS) /\ (NS <> [] -> hrx5_head NS <> nullval)) as Hhd
    by (sep_apply (hrx5_pe_head_ptr NS); entailer!).
  destruct Hhd as [Hhp Hhn].
  match goal with H: hrx5_inv _ _ _ _ _ _ _ _ _ |- _ => pose proof H as Hinv end.
  forward.
  forward_call (gv, Tsh, l_itd L, T, hrx5_head NS, NS, nullval, PS, Int.zero, S, w).
  { destruct Hinv as (Hpok & Hwf & _ & _ & Hnp & _). split; auto. split; [apply hrx5_pe_owners; auto |].
    (* common4 v4.1: every owner's slots NULL or pool entries (NULL here: hrx5_pok) *)
    eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] Hx. cbn in Hx |- *.
    destruct Hx as (_&_&_&_&_&_&_&_&Hc&Hp&Hn). rewrite Hc, Hp, Hn. repeat constructor; left; reflexivity. }
  Intros KD.
  change (negb (Int.eq Int.zero Int.zero)) with false. rewrite hrx5_pe_kents_PS0.
  forward.
  forward_call tt.
  Intros st.
  forward.
  unfold hrx5_SE.
  Exists R sec birth (kents_S S KD) w NS. Exists PS (kents_T T KD) head nk (map kd_kent KD) st.
  rewrite hrx5_pe_khead.
  unfold hrx5_wcore, hrx5_rest, hrx5_globs, hrx5_rglobs, hrx5_lvars, hrx5_scr; cbn [app].
  assert (Hb: s_boot (kents_S S KD) = s_boot S) by (destruct KD; reflexivity).
  rewrite Hb.
  entailer!.
  - split; [| apply hrx5_pe_inv; auto].
    unfold hrx5_base_ok in *. rewrite Hb. exact H.
  - rewrite hrx5_pe_khead. cbn [kents_rep hrx5_khead]. entailer!.
Qed.

End PE.
