(* law handshake_receive: body proofs of local
   functions of the harness unit (hrx5_spec.v), at the unit's compspecs HRX.  receive.c's wg_receive_handshake_packet.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_lem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_C.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_LV.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_N.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_I.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_RS.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_recv_T.
Local Open Scope logic.

#[local] Existing Instance HRX.

(* ---- the composition of the segments (hrx5_recv_defs.v) ---- *)

Definition hrx5_rv_hide : Type := compspecs.

Lemma hrx5_rv_retonly_ok {Espec: OracleKind} (cs: compspecs) Delta P c R R' :
  RA_return R' = RA_return R -> @semax cs Espec Delta P c (hrx5_rv_retonly R) -> @semax cs Espec Delta P c R'.
Proof.
  intros E H. eapply semax_post; [| | | | exact H]; simpl; intros; try (apply andp_left2; apply FF_left).
  rewrite E. apply andp_left2. apply derives_refl.
Qed.

Lemma hrx5_rv_over_switch X : overridePost FF (switch_ret_assert X) = switch_ret_assert X.
Proof. destruct X; reflexivity. Qed.

Lemma hrx5_rv_return_over Q R : RA_return (overridePost Q R) = RA_return R.
Proof. destruct R; reflexivity. Qed.

Definition hrx5_rv_SWa : statement := Eval cbv beta iota delta [hrx5_rv_SW] in
  match hrx5_rv_SW with Ssequence a _ => a | _ => Sskip end.
Definition hrx5_rv_SWb : statement := Eval cbv beta iota delta [hrx5_rv_SW] in
  match hrx5_rv_SW with Ssequence _ (Ssequence b _) => b | _ => Sskip end.
Definition hrx5_rv_SWe : expr := Eval cbv beta iota delta [hrx5_rv_SW] in
  match hrx5_rv_SW with Ssequence _ (Ssequence _ (Sswitch e _)) => e | _ => Econst_int Int.zero tint end.
Lemma hrx5_rv_SW_eq : hrx5_rv_SW = Ssequence hrx5_rv_SWa (Ssequence hrx5_rv_SWb
  (Sswitch hrx5_rv_SWe (LScons (Some 1) hrx5_rv_C1 (LScons (Some 2) hrx5_rv_C2 LSnil)))).
Proof. reflexivity. Qed.

Definition hrx5_rv_MSG1 : statement := Eval cbv beta iota delta [hrx5_rv_C1] in
  match hrx5_rv_C1 with Ssequence a _ => a | _ => Sskip end.
Definition hrx5_rv_NCE1 : expr := Eval cbv beta iota delta [hrx5_rv_C1] in
  match hrx5_rv_C1 with Ssequence _ (Ssequence (Sifthenelse e _ _) _) => e | _ => Econst_int Int.zero tint end.
Lemma hrx5_rv_C1_eq : hrx5_rv_C1 =
  Ssequence hrx5_rv_MSG1 (Ssequence (Sifthenelse hrx5_rv_NCE1 hrx5_rv_NC1 Sskip) hrx5_rv_IREST).
Proof. reflexivity. Qed.
Definition hrx5_rv_MSG2 : statement := Eval cbv beta iota delta [hrx5_rv_C2] in
  match hrx5_rv_C2 with Ssequence a _ => a | _ => Sskip end.
Definition hrx5_rv_NCE2 : expr := Eval cbv beta iota delta [hrx5_rv_C2] in
  match hrx5_rv_C2 with Ssequence _ (Ssequence (Sifthenelse e _ _) _) => e | _ => Econst_int Int.zero tint end.
Lemma hrx5_rv_C2_eq : hrx5_rv_C2 =
  Ssequence hrx5_rv_MSG2 (Ssequence (Sifthenelse hrx5_rv_NCE2 hrx5_rv_NC2 Sskip) hrx5_rv_RREST).
Proof. reflexivity. Qed.

Lemma hrx5_rv_tw12 msg : hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  (hrx5_tw msg = Int.one /\ Zlength msg = 148) \/ (hrx5_tw msg = Int.repr 2 /\ Zlength msg = 92).
Proof.
  unfold hrx5_fwd. intros H H3. apply andb_prop in H as [_ H].
  apply orb_prop in H as [H | H]; [apply orb_prop in H as [H | H] |].
  - apply andb_prop in H as [E L]. apply Int.same_if_eq in E. apply Z.eqb_eq in L. auto.
  - apply andb_prop in H as [E L]. apply Int.same_if_eq in E. apply Z.eqb_eq in L. auto.
  - apply andb_prop in H as [E _]. rewrite E in H3. discriminate.
Qed.

Lemma hrx5_rv_body_eq : unfold_Ssequence hrx5_rv_body =
  unfold_Ssequence (Ssequence (Ssequence (Sset HRC._peer (Ecast (Econst_int (Int.repr 0) tint) (tptr tvoid)))
    (Ssequence (Sset HRC._t'20 (Efield (Ederef (Etempvar HRC._skb (tptr (Tstruct HRC._sk_buff noattr)))
                     (Tstruct HRC._sk_buff noattr)) HRC._data (tptr tuchar)))
       (Ssequence (Sset HRC._t'21 (Efield (Ederef (Ecast (Etempvar HRC._t'20 (tptr tuchar))
                     (tptr (Tstruct HRC._message_header noattr))) (Tstruct HRC._message_header noattr)) HRC._type tuint))
          (Sifthenelse (Ebinop Oeq (Etempvar HRC._t'21 tuint) (Ecast (Econst_int (Int.repr 3) tint) tuint) tint)
             hrx5_rv_COOKIE Sskip))))
    (Ssequence hrx5_rv_LV (Ssequence hrx5_rv_SW hrx5_rv_TAIL))).
Proof. reflexivity. Qed.

Lemma hrx5_body_receive x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_receive_handshake_packet
    (hrx5_receive_spec x25519 aead_dec xaead_enc xaead_dec CSw).
Proof.
  intros HX HA HXA.
  start_function.
  match goal with C: compspecs |- _ => change hrx5_rv_hide in C end.
  assert (HY: hrx5_rv_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec W shd wg head shs s shm msg)
    by exact (conj HX (conj HA (conj HXA (conj SH (conj SH0 (conj SH1 (conj H (conj H0 H1)))))))).
  unfold abbreviate in MORE_COMMANDS. subst MORE_COMMANDS.
  match goal with |- semax _ _ ?c _ => change c with hrx5_rv_body end.
  eapply (semax_unfold_Ssequence _ _ (eq_sym hrx5_rv_body_eq)).
  unfold abbreviate in POSTCONDITION. subst POSTCONDITION.
  change (frame_ret_assert _ _) with (hrx5_rv_R x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg).
  assert (Hn: 4 <= Zlength msg)
    by (unfold hrx5_fwd in H; destruct (4 <=? Zlength msg) eqn:E; [apply Z.leb_le in E; lia | discriminate]).
  assert (Hp: isptr (sk_data s)) by (destruct H0 as [_ Hmc]; destruct (sk_data s); try contradiction; exact I).
  (* peer = NULL; the type word; the cookie reply *)
  eapply semax_seq with (Q := PROP (Int.eq (hrx5_tw msg) (Int.repr 3) = false)
    LOCAL (temp HRC._peer nullval; gvars gv; temp HRC._wg wg; temp HRC._skb sp)
    SEP (rxw_rep CSw gv shd wg head W; qlen_rep gv q; skb_rep shs sp s; bytes_at shm msg (sk_data s); wg_consts gv;
         mem_mgr gv)).
  { abbreviate_semax. forward.
    unfold skb_rep. Intros. rewrite hrx5_rvl_skb_cs.
    rewrite (hrx5_rvl_split shm msg) by (destruct H0; auto). Intros.
    unfold skb_val. forward. forward.
    forward_if.
    { eapply semax_pre; [| eapply hrx5_rv_retonly_ok; [| exact (hrx5_rv_C_ok Espec x25519 aead_enc aead_dec xaead_enc
          xaead_dec CSw gv W q shd wg head shs sp s shm msg HY ltac:(match goal with Hq: hrx5_tw msg = _ |- _ => rewrite Hq; apply Int.eq_true end))]].
      2: reflexivity.
      unfold hrx5_rv_S0, skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. }
    { forward. unfold hrx5_rv_R; cbn [RA_normal frame_ret_assert function_body_ret_assert].
      unfold skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. apply Int.eq_false; auto. } }
  (* the load, validate, the verdict *)
  Intros. rename H2 into Htw3.
  eapply semax_seq.
  { eapply semax_pre; [| exact (hrx5_rv_LV_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head
      shs sp s shm msg HY Htw3)].
    unfold hrx5_rv_S0. entailer!. }
  (* the switch; the tail *)
  eapply semax_seq with (Q := hrx5_rv_Qtail x25519 aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg);
    [| exact (hrx5_rv_T_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg HY)].
  unfold hrx5_rv_SV. Intros r.
  rewrite hrx5_rv_SW_eq. unfold hrx5_rv_SWa, hrx5_rv_SWb.
  abbreviate_semax.
  unfold skb_rep. Intros. rewrite hrx5_rvl_skb_cs. rewrite (hrx5_rvl_split shm msg) by (destruct H0; auto). Intros.
  unfold skb_val. forward. forward.
  destruct (hrx5_rv_tw12 msg H Htw3) as [[Etw Elen] | [Etw Elen]].
  - (* case 1: an initiation *)
    apply (semax_switch_PQR 1); [reflexivity | entailer! | entailer!; rewrite Etw; reflexivity | ].
    change (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr 1))
      (LScons (Some 1) hrx5_rv_C1 (LScons (Some 2) hrx5_rv_C2 LSnil)))) with (Ssequence hrx5_rv_C1 (Ssequence hrx5_rv_C2 Sskip)).
    eapply semax_seq with (Q := FF); [| apply semax_ff].
    rewrite hrx5_rv_C1_eq. unfold hrx5_rv_MSG1, hrx5_rv_NCE1.
    forward. forward.
    forward_if (hrx5_rv_SC HRC._message (Int.eq (hrx5_tw msg) Int.one = true /\ hrx5_rv_cons W q s msg r = true)
      CSw gv W q shd wg head shs sp s shm msg r).
    { assert (Enc: hrx5_rv_nc W q s msg r = true) by (destruct (hrx5_rv_nc W q s msg r); [reflexivity | inv H5]).
      eapply semax_pre; [| eapply hrx5_rv_retonly_ok; [| exact (hrx5_rv_N1_ok Espec x25519 aead_enc aead_dec xaead_enc
        xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY)]]; [| reflexivity].
      unfold hrx5_rv_SC, skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. rewrite Etw. auto. }
    { assert (Enc: hrx5_rv_nc W q s msg r = false) by (destruct (hrx5_rv_nc W q s msg r); [inv H5 | reflexivity]).
      rewrite Enc, orb_false_r in H3.
      forward.
      unfold hrx5_rv_R; cbn [RA_normal frame_ret_assert function_body_ret_assert switch_ret_assert].
      unfold hrx5_rv_SC, skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. rewrite Etw. auto. }
    exact (hrx5_rv_I_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY).
  - (* case 2: a response *)
    apply (semax_switch_PQR 2); [reflexivity | entailer! | entailer!; rewrite Etw; reflexivity | ].
    change (seq_of_labeled_statement (select_switch (Int.unsigned (Int.repr 2))
      (LScons (Some 1) hrx5_rv_C1 (LScons (Some 2) hrx5_rv_C2 LSnil)))) with (Ssequence hrx5_rv_C2 Sskip).
    eapply semax_seq with (Q := FF); [| apply semax_ff].
    rewrite hrx5_rv_C2_eq. unfold hrx5_rv_MSG2, hrx5_rv_NCE2.
    forward. forward.
    forward_if (hrx5_rv_SC HRC._message__1 (Int.eq (hrx5_tw msg) (Int.repr 2) = true /\ hrx5_rv_cons W q s msg r = true)
      CSw gv W q shd wg head shs sp s shm msg r).
    { assert (Enc: hrx5_rv_nc W q s msg r = true) by (destruct (hrx5_rv_nc W q s msg r); [reflexivity | inv H5]).
      eapply semax_pre; [| eapply hrx5_rv_retonly_ok; [| exact (hrx5_rv_N2_ok Espec x25519 aead_enc aead_dec xaead_enc
        xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY)]]; [| reflexivity].
      unfold hrx5_rv_SC, skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. rewrite Etw. auto. }
    { assert (Enc: hrx5_rv_nc W q s msg r = false) by (destruct (hrx5_rv_nc W q s msg r); [inv H5 | reflexivity]).
      rewrite Enc, orb_false_r in H3.
      forward.
      unfold hrx5_rv_R; cbn [RA_normal frame_ret_assert function_body_ret_assert switch_ret_assert].
      unfold hrx5_rv_SC, skb_rep. rewrite hrx5_rvl_skb_cs, (hrx5_rvl_split shm msg) by (destruct H0; auto).
      entailer!. rewrite Etw. auto. }
    exact (hrx5_rv_RS_ok Espec x25519 aead_enc aead_dec xaead_enc xaead_dec CSw gv W q shd wg head shs sp s shm msg r HY).
Qed.

(* the conjunction of this file's body lemmas *)
Definition hrx5_bodies_recv : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_wg_receive_handshake_packet (hrx5_receive_spec x25519 aead_dec xaead_enc xaead_dec CSw)).

Theorem hrx5_grp_recv : hrx5_bodies_recv.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  exact (hrx5_body_receive _ _ _ _ _ _ H1 H2 H3).
Qed.
