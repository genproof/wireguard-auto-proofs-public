(* law handshake_receive, phase B4, segment R:
   statement 25 (the harness's model block) for a response object OResp M.  Port of consume_response_any's
   phase Q3.  This file: helpers, the cut of the statement, the states of the
   response branch RS and the parts' statements.
   Parts: W (table walk), E (entry test), N (node walk), K (state test), C (two copies), M (call + acc_resp),
   O (statement 25 from the core: hrx5_B4_Q -> hrx5_S4); the core and the target: hrx5_B4_R.v. *)
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
#[local] Existing Instance W_handshake_receive.
#[local] Existing Instance W_handshake_receive.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_pure.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B4_R_sep.
Local Open Scope Z_scope.

#[local] Instance hrx5_B4_R_cceH : change_composite_env HCS W_handshake_receive.
Proof. make_cs_preserve HCS W_handshake_receive. Defined.
#[local] Instance hrx5_B4_R_cceK : change_composite_env CKS W_handshake_receive.
Proof. make_cs_preserve CKS W_handshake_receive. Defined.
#[local] Instance hrx5_B4_R_cceN : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.

Lemma hrx5_B4_R_mident_cs sh I p : @data_at HCS sh t_mident (mident_val I) p =
  @data_at W_handshake_receive sh t_mident
    (bytes (mi_priv I), (bytes (mi_pub I), Vint (if mi_ok I then Int.one else Int.zero))) p.
Proof. set (v := mident_val I). rewrite (@data_at_change_composite HCS W_handshake_receive _ sh t_mident v v (JMeq_refl _)); [reflexivity | prove_cs_preserve_type]. Qed.
(* ---------------------------------------------------------------------- *)
(* Helpers: compspecs conversions, an entry of the pool                    *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B4_R_conv_itab sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_handshake_receive sh t_itab v p.
Proof. rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_itab v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hrx5_B4_R_conv_entry sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p =
  @data_at W_handshake_receive sh t_entry_s (entry_val E n h) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_entry_s (entry_val E n h) (entry_val E n h) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_B4_R_conv_resp sh M p :
  @data_at Noise.CS sh t_resp (resp_val M) p =
  @data_at W_handshake_receive sh t_resp (resp_val M) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_handshake_receive _ sh t_resp (resp_val M) (resp_val M) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hrx5_B4_R_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hrx5_B4_R_iter_split L D1 x D2 :
  iter_sepcon (pool_item_rep L) (D1 ++ x :: D2) =
  (pool_item_rep L x * iter_sepcon (pool_item_rep L) (D1 ++ D2))%logic.
Proof.
  rewrite !iter_sepcon_app. simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

Lemma hrx5_B4_R_valid L D a :
  In a (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  iter_sepcon (pool_item_rep L) D |-- valid_pointer a.
Proof.
  intros Ha HF. destruct (hrx5_B4_R_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hrx5_B4_R_iter_split. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at. apply data_at_valid_ptr; [| simpl; lia].
  rewrite Forall_forall in HF. specialize (HF (a, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
  apply readable_nonidentity, writable_readable; exact HF.
Qed.

Lemma hrx5_B4_R_isptr L D a :
  In a (saddrs D) -> iter_sepcon (pool_item_rep L) D |-- !! isptr a.
Proof.
  intros Ha. destruct (hrx5_B4_R_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hrx5_B4_R_iter_split. unfold pool_item_rep, entry_at. entailer!. destruct H; auto.
Qed.

Lemma hrx5_B4_R_ptrs L D : iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [| [[a sh] E] D IH]; [simpl; entailer! |].
  change (iter_sepcon (pool_item_rep L) ((a, sh, E) :: D)) with (pool_item_rep L (a, sh, E) * iter_sepcon (pool_item_rep L) D)%logic.
  rewrite (add_andp _ _ IH). unfold pool_item_rep at 1, entry_at. unfold saddrs; cbn [map]; fold (saddrs D).
  entailer!. all: try (constructor; auto); match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf; auto end.
Qed.

Lemma hrx5_B4_R_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_handshake_receive sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hrx5_B4_R_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite hrx5_B4_R_iter_split. unfold pool_item_rep, entry_at. rewrite hrx5_B4_R_conv_entry. reflexivity.
Qed.

Lemma hrx5_B4_R_succ_in L a : succ_in L a <> nullval -> In (succ_in L a) L.
Proof.
  induction L as [| x L IH]; simpl; intros H; [congruence |].
  destruct (EqDec_val x a).
  - destruct L; simpl in *; [congruence | auto].
  - right. auto.
Qed.

Lemma hrx5_B4_R_succ_pn L a : (forall x, In x L -> isptr x) -> is_pointer_or_null (succ_in L a).
Proof.
  intros HL. destruct (eq_dec (succ_in L a) nullval) as [-> | Hn]; [simpl; auto |].
  specialize (HL _ (hrx5_B4_R_succ_in L a Hn)). destruct (succ_in L a); try contradiction; simpl; auto.
Qed.

Lemma hrx5_B4_R_find_app T L1 L2 idx :
  t_find_index T (L1 ++ L2) idx =
  match t_find_index T L1 idx with None => t_find_index T L2 idx | r => r end.
Proof.
  induction L1 as [| a L1 IH]; simpl; [reflexivity |].
  destruct (t_entry T a) as [E |]; [destruct (Int.eq (e_index E) idx) |]; auto.
Qed.

Lemma hrx5_B4_R_succ_mid L1 a L2 : NoDup (L1 ++ a :: L2) -> succ_in (L1 ++ a :: L2) a = hd nullval L2.
Proof.
  induction L1 as [| x L1 IH]; simpl; intros Hnd.
  - destruct (EqDec_val a a); [reflexivity | congruence].
  - inversion Hnd as [| ? ? Hni Hnd']; subst. destruct (EqDec_val x a) as [-> | Hne].
    + exfalso. apply Hni. apply in_or_app. right. left. reflexivity.
    + apply IH. exact Hnd'.
Qed.

Lemma hrx5_B4_R_lm_snoc l N e :
  hrx5_B4_R_lm (l ++ [N]) e = if eq_dec (hs_addr (hn_p N)) e then hn_addr N else hrx5_B4_R_lm l e.
Proof. unfold hrx5_B4_R_lm. rewrite fold_left_app. reflexivity. Qed.

Lemma hrx5_B4_R_off48 x : isptr x -> offset_val 0 (offset_val 48 x) = hs_addr x.
Proof.
  intros Hx. destruct x; try contradiction. unfold hs_addr, OFS_PEER_HANDSHAKE. simpl.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma hrx5_B4_R_wand1 (A Q: mpred) : (A * (A -* Q) |-- Q)%logic.
Proof. apply wand_frame_elim. Qed.

Lemma hrx5_B4_R_sn_hs T a E H : sn_hs (snap_of T a E H) = H.
Proof. reflexivity. Qed.

Lemma hrx5_B4_R_split_T bs p : hbytes Tsh bs p |-- (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.
Lemma hrx5_B4_R_join_T bs p : (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic |-- hbytes Tsh bs p.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.

Lemma hrx5_B4_R_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros Hs. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

Lemma hrx5_B4_R_entry_next E n h :
  (let (x, _) := let (_, y) := entry_val E n h in y in x) = n.
Proof. reflexivity. Qed.

Lemma hrx5_B4_R_sfind_mid {A: Type} (D1 D2: list (val * share * A)) a sh E :
  NoDup (saddrs (D1 ++ (a, sh, E) :: D2)) -> sfind (D1 ++ (a, sh, E) :: D2) a = Some (sh, E).
Proof.
  induction D1 as [| [[x shx] Ex] D1 IH]; simpl; intros Hnd.
  - destruct (EqDec_val a a); [reflexivity | congruence].
  - inversion Hnd as [| ? ? Hni Hnd']; subst. destruct (EqDec_val x a) as [-> | Hne].
    + exfalso. apply Hni. unfold saddrs. rewrite map_app. apply in_or_app. right. left. reflexivity.
    + apply IH. exact Hnd'.
Qed.

Lemma hrx5_B4_R_focus2 L D e :
  In e (saddrs D) -> NoDup (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\ sfind D e = Some (sh, E) /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_handshake_receive sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha Hnd HF. destruct (hrx5_B4_R_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split; [| split].
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - apply hrx5_B4_R_sfind_mid; exact Hnd.
  - rewrite hrx5_B4_R_iter_split. unfold pool_item_rep, entry_at. rewrite hrx5_B4_R_conv_entry. reflexivity.
Qed.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* The cut of hrx5_B4_M for a response object (kind 2)                     *)
(* ---------------------------------------------------------------------- *)

(* hrx5_B4_M = C97; if (t'97) IB else ELSE   (C97: the initiation test, 0 for kind 2) *)
Definition hrx5_B4_R_c97 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_M] in
  (match hrx5_B4_M with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_e97 : expr := ltac:(let x := eval cbv beta iota delta [hrx5_B4_M] in
  (match hrx5_B4_M with Ssequence _ (Sifthenelse c _ _) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hrx5_B4_R_IB : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_M] in
  (match hrx5_B4_M with Ssequence _ (Sifthenelse _ t _) => t | _ => Sskip end) in exact x).
Definition hrx5_B4_R_ELSE : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_M] in
  (match hrx5_B4_M with Ssequence _ (Sifthenelse _ _ e) => e | _ => Sskip end) in exact x).
(* ELSE = C94; if (t'94) RS else CK   (C94: fwd && kind == 2 && id.ok) *)
Definition hrx5_B4_R_c94 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_ELSE] in
  (match hrx5_B4_R_ELSE with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_e94 : expr := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_ELSE] in
  (match hrx5_B4_R_ELSE with Ssequence _ (Sifthenelse c _ _) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hrx5_B4_R_RS : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_ELSE] in
  (match hrx5_B4_R_ELSE with Ssequence _ (Sifthenelse _ t _) => t | _ => Sskip end) in exact x).
Definition hrx5_B4_R_CK : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_ELSE] in
  (match hrx5_B4_R_ELSE with Ssequence _ (Sifthenelse _ _ e) => e | _ => Sskip end) in exact x).
(* RS = (e = itd.head; for (;;) B1 I1); if86; if (t'86) HS *)
Definition hrx5_B4_R_se : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence (Ssequence s _) _ => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_B1 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence (Ssequence _ (Sloop b _)) _ => b | _ => Sskip end) in exact x).
Definition hrx5_B4_R_I1 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence (Ssequence _ (Sloop _ i)) _ => i | _ => Sskip end) in exact x).
Definition hrx5_B4_R_if86 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_c86 : expr := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence _ (Ssequence _ (Sifthenelse c _ _)) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hrx5_B4_R_HS : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_RS] in
  (match hrx5_B4_R_RS with Ssequence _ (Ssequence _ (Sifthenelse _ t _)) => t | _ => Sskip end) in exact x).
(* HS = (nd = peers; for (;;) B2 I2); if85; if (t'85) CALL *)
Definition hrx5_B4_R_sit : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence (Ssequence s _) _ => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_B2 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence (Ssequence _ (Sloop b _)) _ => b | _ => Sskip end) in exact x).
Definition hrx5_B4_R_I2 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence (Ssequence _ (Sloop _ i)) _ => i | _ => Sskip end) in exact x).
Definition hrx5_B4_R_if85 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_c85 : expr := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence _ (Ssequence _ (Sifthenelse c _ _)) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hrx5_B4_R_CALL : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_HS] in
  (match hrx5_B4_R_HS with Ssequence _ (Ssequence _ (Sifthenelse _ t _)) => t | _ => Sskip end) in exact x).
(* CALL = bytes_copy(before.ck, ..); bytes_copy(before.h, ..); t'84 = m_consume_response(..); acc_resp = t'84 *)
Definition hrx5_B4_R_bc1 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_CALL] in
  (match hrx5_B4_R_CALL with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_bc2 : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_CALL] in
  (match hrx5_B4_R_CALL with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_mcall : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_CALL] in
  (match hrx5_B4_R_CALL with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end) in exact x).
Definition hrx5_B4_R_asg : statement := ltac:(let x := eval cbv beta iota delta [hrx5_B4_R_CALL] in
  (match hrx5_B4_R_CALL with Ssequence _ (Ssequence _ (Ssequence _ s)) => s | _ => Sskip end) in exact x).

Lemma hrx5_B4_R_M_eq : hrx5_B4_M = Ssequence hrx5_B4_R_c97 (Sifthenelse hrx5_B4_R_e97 hrx5_B4_R_IB hrx5_B4_R_ELSE).
Proof. reflexivity. Qed.
Lemma hrx5_B4_R_else_eq : hrx5_B4_R_ELSE = Ssequence hrx5_B4_R_c94 (Sifthenelse hrx5_B4_R_e94 hrx5_B4_R_RS hrx5_B4_R_CK).
Proof. reflexivity. Qed.
Lemma hrx5_B4_R_rb_eq : hrx5_B4_R_RS =
  Ssequence (Ssequence hrx5_B4_R_se (Sloop hrx5_B4_R_B1 hrx5_B4_R_I1))
    (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip)).
Proof. reflexivity. Qed.
Lemma hrx5_B4_R_hs_eq : hrx5_B4_R_HS =
  Ssequence (Ssequence hrx5_B4_R_sit (Sloop hrx5_B4_R_B2 hrx5_B4_R_I2))
    (Ssequence hrx5_B4_R_if85 (Sifthenelse hrx5_B4_R_c85 hrx5_B4_R_CALL Sskip)).
Proof. reflexivity. Qed.
Lemma hrx5_B4_R_call_eq : hrx5_B4_R_CALL =
  Ssequence hrx5_B4_R_bc1 (Ssequence hrx5_B4_R_bc2 (Ssequence hrx5_B4_R_mcall hrx5_B4_R_asg)).
Proof. reflexivity. Qed.

Lemma hrx5_B4_R_post {Espec: OracleKind} {cs: compspecs} Delta P c (Q Q': environ -> mpred) R :
  ENTAIL Delta, Q |-- Q' -> semax Delta P c (overridePost Q R) -> semax Delta P c (overridePost Q' R).
Proof.
  intros HE Hs. eapply semax_post; [| | | | exact Hs]; destruct R; simpl; auto;
    intros; apply andp_left2, derives_refl.
Qed.

Ltac hrx5_B4_R_vp := first [ apply hrx5_B4_R_valid; solve [auto]
                           | apply sepcon_valid_pointer2; hrx5_B4_R_vp
                           | apply sepcon_valid_pointer1; hrx5_B4_R_vp ].

Lemma hrx5_B4_R_sepx {A: Type} (x1 x2 x3 x4 x5 x6 x7 x8: mpred) (B: list mpred) :
  @SEPx A [x1; x2; x3; x4; x5; x6; x7; x8; fold_right_sepcon B] = SEPx (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: B).
Proof. unfold SEPx. extensionality rho. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* The states of the response branch RS                                    *)
(* ---------------------------------------------------------------------- *)

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).

(* the locals the block keeps (acc_resp, target and the loop temps are listed in front); kind = 2, fwd = 1,
   mr = m, acc_init = 0 *)
Definition hrx5_B4_R_Q gv L (nk: val) (KE: list kent4) (st i: Z) (S: shim) (lul: int64) (m img: val) (n: Z) (tw: int)
  : list localdef :=
  hrx5_ltemps nk KE st i S lul ++
  [temp HM._buf nullval; temp HM._mi nullval; temp HM._mr m; temp HM._mc nullval;
   temp HM._img img; temp HM._len (Vlong (Int64.repr n)); temp HM._kind (Vint (Int.repr 2));
   temp HM._tw (Vint tw); temp HM._fwd (Vint Int.one); temp HM._acc_init (Vint Int.zero)] ++
  hrx5_lvars gv L.

(* the SEP items the block reads, then an opaque frame FX *)
Definition hrx5_B4_R_R gv L IA NS NSs T m M (st: mpred) FX : list mpred :=
  [@data_at HCS Tsh t_mident (mident_val IA) (l_id L); itable Tsh (l_itd L) T;
   @data_at W Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L); hnodes_rep4 W (hrx5_head NS) NSs;
   resp_rep Ews m M; wg_consts gv; st; @data_at_ HCS Tsh t_mstate (l_before L); FX].

(* the start of RS *)
Definition hrx5_B4_R_A0 gv L nk KE st i S lul m img n tw IA NS NSs T M FX : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._acc_resp (Vint Int.zero) :: temp HM._target nullval ::
                    hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* the table walk's result *)
Definition hrx5_B4_R_ef (T: tstate) (idx: int) : val :=
  match t_find_index T (t_L T) idx with None => nullval | Some (a, _) => a end.

Definition hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._e (hrx5_B4_R_ef T (rm_receiver M)) :: temp HM._acc_resp (Vint Int.zero) ::
                    temp HM._target nullval :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* a handshake entry a was found: the node walk's start *)
Definition hrx5_B4_R_A3 gv L nk KE st i S lul m img n tw IA NS NSs T M FX (a: val) : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._e a :: temp HM._acc_resp (Vint Int.zero) :: temp HM._target nullval ::
                    hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* after the node walk: target = p *)
Definition hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX (a p: val) : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) ::
                    hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* after if85: t'85 = the snapshot state test *)
Definition hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX (a p: val) (b: int) : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._t'85 (Vint b) :: temp HM._target p :: temp HM._e a ::
                    temp HM._acc_resp (Vint Int.zero) :: hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* after the two copies: before = the snapshot's chaining key and hash *)
Definition hrx5_B4_R_A6 gv L nk KE st i S lul m img n tw IA NS NSs T M FX (a p: val) (ck h: list byte)
  : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) ::
                    hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [@data_at HCS Tsh t_mident (mident_val IA) (l_id L); itable Tsh (l_itd L) T;
         @data_at W Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L); hnodes_rep4 W (hrx5_head NS) NSs;
         resp_rep Ews m M; wg_consts gv; @data_at_ HCS Tsh t_mstate (l_st L);
         @data_at HCS Tsh t_mstate (mstate_val ck h) (l_before L); FX])).

(* after m_consume_response: mc = the model's result *)
Definition hrx5_B4_R_A8 gv L nk KE st i S lul m img n tw IA NS NSs T M FX (a p: val) (ck h: list byte)
  (mc: option (list byte * list byte)) : environ -> mpred :=
  PROPx [] (LOCALx (temp HM._t'84 (Vint (match mc with Some _ => Int.one | None => Int.zero end)) ::
                    temp HM._target p :: temp HM._e a :: temp HM._acc_resp (Vint Int.zero) ::
                    hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx [@data_at HCS Tsh t_mident (mident_val IA) (l_id L); itable Tsh (l_itd L) T;
         @data_at W Tsh (tptr t_hnode4) (hrx5_head NS) (l_peers L); hnodes_rep4 W (hrx5_head NS) NSs;
         resp_rep Ews m M; wg_consts gv;
         match mc with
         | Some (ck', h') => @data_at HCS Tsh t_mstate (mstate_val ck' h') (l_st L)
         | None => @data_at_ HCS Tsh t_mstate (l_st L) end;
         @data_at HCS Tsh t_mstate (mstate_val ck h) (l_before L); FX])).

(* the end of RS: acc_resp and target as hrx5_acc_ok wants them (OResp, fwd), st as hrx5_st_rep *)
Definition hrx5_B4_R_acc (IA: mident) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg)
  (NS: list hnode4) (tg: val) (ar: Z) : Prop :=
  match hrx5cr_tgt x25519 aead_dec IA T PS M with
  | Some (a, _, _, _) => ar = 1 /\ tg = hrx5_nfind NS a
  | None => ar = 0 /\ (tg = nullval \/ In tg (map hn_addr NS))
  end.
Definition hrx5_B4_R_strep (IA: mident) (T: tstate) (PS: list (val * share * peer)) (M: resp_msg) (st: val)
  : mpred :=
  match hrx5cr_tgt x25519 aead_dec IA T PS M with
  | Some (_, _, ck, h) => @data_at HCS Tsh t_mstate (mstate_val ck h) st
  | None => @data_at_ HCS Tsh t_mstate st
  end.

Definition hrx5_B4_R_OUT gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX : environ -> mpred :=
  EX tg: val, EX ar: Z,
  PROPx [hrx5_B4_R_acc IA T PS M NS tg ar]
  (LOCALx (temp HM._acc_resp (Vint (Int.repr ar)) :: temp HM._target tg ::
           hrx5_B4_R_Q gv L nk KE st i S lul m img n tw)
  (SEPx (hrx5_B4_R_R gv L IA NS NSs T m M (hrx5_B4_R_strep IA T PS M (l_st L)) FX))).

End States.

(* freeze everything but the items K (found by syntactic equality; VST's `freeze F := - a b` unifies the
   patterns with the whole goal and normalizes the SEP list by cbv: minutes on these states) *)
Ltac hrx5_B4_R_idx R a :=
  lazymatch R with
  | a :: _ => constr:(0%Z)
  | _ :: ?R' => let n := hrx5_B4_R_idx R' a in constr:(Z.succ n)
  end.
Ltac hrx5_B4_R_len R :=
  lazymatch R with
  | nil => constr:(O)
  | _ :: ?R' => let n := hrx5_B4_R_len R' in constr:(S n)
  end.
Ltac hrx5_B4_R_keep_tac K name :=
  lazymatch goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let rec idxs l := lazymatch l with
      | nil => constr:(@nil Z)
      | ?a :: ?l' => let i := hrx5_B4_R_idx R a in let r := idxs l' in constr:(i :: r) end in
    let A := idxs K in
    let n := hrx5_B4_R_len R in
    let A' := eval compute in (Zlist_complement n A) in
    freeze_tac A' name
  end.
Tactic Notation "hrx5_B4_R_keep" constr(K) ident(name) := hrx5_B4_R_keep_tac K name.

(* Opaque atoms for the opened node and the opened message: a term `@data_at W .. t_hnode4 (.., hsnap_val ..)`
   costs a kernel reptype conversion (HCS -> W) at each of its occurrences in a proof term, and the wrappers
   below carry their SEP through many steps; as atoms they cost nothing. *)
Definition hrx5_B4_R_nodeA (N: hnode4) (nx: val) : mpred :=
  @data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N).
Definition hrx5_B4_R_nodeR (N: hnode4) (nx: val) (H: handshake) : mpred :=
  ((hbytes Ews (hs_eph H) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk H) (offset_val 184 (hn_addr N)) *
    hbytes Ews (hs_hash H) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck H) (offset_val 248 (hn_addr N))) -*
   hrx5_B4_R_nodeA N nx)%logic.
Definition hrx5_B4_R_respR (M: resp_msg) (m: val) : mpred :=
  ((hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m)) -*
   @data_at W Ews t_resp (resp_val M) m)%logic.

Lemma hrx5_B4_R_open NSs NSa N0 NSb : NSs = NSa ++ N0 :: NSb ->
  hnodes_rep4 W (hrx5_head NSs) NSs |--
  (hrx5_B4_R_nodeA N0 (hrx5_head NSb) * (hrx5_B4_R_nodeA N0 (hrx5_head NSb) -* hnodes_rep4 W (hrx5_head NSs) NSs))%logic.
Proof.
  intros ->. destruct hrx5_B4_R_sep_ok as (Snode & _). unfold hrx5_B4_R_nodeA. apply Snode.
Qed.

Lemma hrx5_B4_R_fields T N nx p P : hn_snap N = hsnap_val (hs_snap_cur T p P) -> hs_ok (p_hs P) ->
  hrx5_B4_R_nodeA N nx |--
  (hbytes Ews (hs_eph (p_hs P)) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk (p_hs P)) (offset_val 184 (hn_addr N)) *
   hbytes Ews (hs_hash (p_hs P)) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck (p_hs P)) (offset_val 248 (hn_addr N)) *
   hrx5_B4_R_nodeR N nx (p_hs P))%logic.
Proof.
  intros Hs Hok. destruct hrx5_B4_R_sep_ok as (_ & Sfields & _).
  unfold hrx5_B4_R_nodeR, hrx5_B4_R_nodeA. rewrite Hs.
  exact (Sfields Ews (hn_p N) (hs_snap_cur T p P) (hn_refs N) (hn_rest N) nx (hn_addr N) Hok).
Qed.

Lemma hrx5_B4_R_unfields N nx H :
  (hbytes Ews (hs_eph H) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk H) (offset_val 184 (hn_addr N)) *
   hbytes Ews (hs_hash H) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck H) (offset_val 248 (hn_addr N)) *
   hrx5_B4_R_nodeR N nx H)%logic |-- hrx5_B4_R_nodeA N nx.
Proof. unfold hrx5_B4_R_nodeR. apply wand_frame_elim. Qed.

Lemma hrx5_B4_R_resp_open M m :
  resp_rep Ews m M |--
  (!! rm_ok M && (hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m) *
                  hrx5_B4_R_respR M m))%logic.
Proof.
  destruct hrx5_B4_R_sep_ok as (_ & _ & _ & _ & Sresp & _).
  unfold resp_rep. apply derives_extract_prop; intro HM. rewrite hrx5_B4_R_conv_resp. unfold hrx5_B4_R_respR.
  apply andp_right; [apply prop_right; exact HM |]. apply Sresp; exact HM.
Qed.

Lemma hrx5_B4_R_resp_close M m : rm_ok M ->
  (hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m) * hrx5_B4_R_respR M m)%logic
  |-- resp_rep Ews m M.
Proof.
  intros HM. unfold resp_rep. apply andp_right; [apply prop_right; exact HM |].
  rewrite hrx5_B4_R_conv_resp. unfold hrx5_B4_R_respR. apply wand_frame_elim.
Qed.

(* ---------------------------------------------------------------------- *)
(* The parts (children's targets); D = hrx5_Delta x25519 aead_dec xaead_enc xaead_dec                      *)
(* ---------------------------------------------------------------------- *)

(* W: e = itd.head; for (; e && e->index != mr->receiver_index; e = e->next);   (port: hcr5_q3_Lwalk) *)
Definition hrx5_B4_R_W_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs T M FX Rr,
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_R_A0 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
    (Ssequence hrx5_B4_R_se (Sloop hrx5_B4_R_B1 hrx5_B4_R_I1))
    (overridePost (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX) Rr).

(* E: if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) HS: not found / not a handshake entry / a handshake
   entry (then HS)   (port: hcr5_q3_Lnf, hcr5_q3_Lnhs, hcr5_q3_Lhs) *)
Definition hrx5_B4_R_E_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr,
  (mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = None ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
     (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)) /\
  (forall a E, mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
   Int.eq (e_type E) IDX_HANDSHAKE = false ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
     (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)) /\
  (forall a E, t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
   Int.eq (e_type E) IDX_HANDSHAKE = true ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A3 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a) hrx5_B4_R_HS
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A1 gv L nk KE st i S lul m img n tw IA NS NSs T M FX)
     (Ssequence hrx5_B4_R_if86 (Sifthenelse hrx5_B4_R_c86 hrx5_B4_R_HS Sskip))
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)).

(* N: nd = peers; for (; nd; nd = nd->next) if (&nd->p->handshake.entry == e) target = nd;   (port: hcr5_q3_Lnode) *)
Definition hrx5_B4_R_N_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs T M FX a Rr,
  hrx5_head NSs = hrx5_head NS -> In a (saddrs (t_D T)) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_R_A3 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a)
    (Ssequence hrx5_B4_R_sit (Sloop hrx5_B4_R_B2 hrx5_B4_R_I2))
    (overridePost (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hrx5_B4_R_lm NSs a)) Rr).

(* K: if (target != NULL && target->snap.state == HANDSHAKE_CREATED_INITIATION) CALL: the test (on the node of
   the entry's peer), the state is not / is CREATED_INITIATION   (port: hcr5_q3_L23, L23n, L23c) *)
Definition hrx5_B4_R_K_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr,
  (forall a E NSa N0 NSb P,
   NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
   hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) -> hrx5_head NSs = hrx5_head NS ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0)) hrx5_B4_R_if85
     (overridePost (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0)
        (if Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION then Int.one else Int.zero)) Rr)) /\
  (forall a E p shp P,
   mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
   Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
   Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = false -> In p (map hn_addr NS) ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p Int.zero)
     (Sifthenelse hrx5_B4_R_c85 hrx5_B4_R_CALL Sskip)
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)) /\
  (forall a p,
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p) hrx5_B4_R_CALL
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A7 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a p Int.one)
     (Sifthenelse hrx5_B4_R_c85 hrx5_B4_R_CALL Sskip)
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)).

(* C: the two copies into before, then the rest of CALL   (port: hcr5_q3_LBC) *)
Definition hrx5_B4_R_C_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX
    a E NSa N0 NSb P rest Rr,
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) -> hs_ok (p_hs P) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) -> hrx5_head NSs = hrx5_head NS ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_R_A6 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
    rest (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_R_A4 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0))
    (Ssequence hrx5_B4_R_bc1 (Ssequence hrx5_B4_R_bc2 rest))
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr).

(* M: t'84 = m_consume_response(..); acc_resp = t'84   (port: hcr5_q3_LMC1, hcr5_q3_LMC2) *)
Definition hrx5_B4_R_M_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX Rr,
  (forall a E NSa N0 NSb P,
   NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
   hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
   hrx5_head NSs = hrx5_head NS -> hs_ok (p_hs P) -> Zlength (mi_priv IA) = 32 ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A6 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
     hrx5_B4_R_mcall
     (overridePost (hrx5_B4_R_A8 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a (hn_addr N0)
        (hs_ck (p_hs P)) (hs_hash (p_hs P))
        (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
           (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M))) Rr)) /\
  (forall a E x shp P,
   mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
   Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
   Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = true ->
   x = hrx5_nfind NS (e_peer E) -> In x (map hn_addr NS) ->
   semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
     (hrx5_B4_R_A8 gv L nk KE st i S lul m img n tw IA NS NSs T M FX a x (hs_ck (p_hs P)) (hs_hash (p_hs P))
        (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
           (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)))
     hrx5_B4_R_asg
     (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS NSs PS T M FX) Rr)).

(* the response branch RS from A0 to OUT (proved in hrx5_B4_R.v from W E N K C M, port of hcr5_q3_all) *)
Definition hrx5_B4_R_core_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_dec xaead_enc xaead_dec gv L nk KE st i S lul m img n tw IA KA NS PS T M FX Rr,
  mi_ok IA = true -> Zlength (mi_priv IA) = 32 -> itable_wf T -> Forall isptr (saddrs (t_D T)) ->
  hrx5cr_pool KA PS T -> hnodes_peers4 NS PS -> NoDup (map peer_addr4 PS) ->
  Forall (fun x => match x with (_, _, P) => hs_ok (p_hs P) end) PS ->
  Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x)) PS ->
  Forall isptr (map hn_addr (hnodes_snapped4 T NS PS)) ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_R_A0 gv L nk KE st i S lul m img n tw IA NS (hnodes_snapped4 T NS PS) T M FX) hrx5_B4_R_RS
    (overridePost (hrx5_B4_R_OUT x25519 aead_dec gv L nk KE st i S lul m img n tw IA NS (hnodes_snapped4 T NS PS)
       PS T M FX) Rr).

(* O: the whole statement 25 for OResp M from the core: the initiation test (0), fwd && kind == 2 && id.ok,
   the cookie test (0), RS by the core when taken; hrx5_B4_Q -> hrx5_S4 *)
Definition hrx5_B4_R_O_stmt : Prop :=
  forall {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port M dp img,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hrx5_B4_R_core_stmt ->
  semax (hrx5_Delta x25519 aead_dec xaead_enc xaead_dec)
    (hrx5_B4_Q x25519 gv L FR R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port (OResp M) dp img)
    hrx5_B4_M
    (overridePost (hrx5_S4 x25519 aead_dec xaead_dec gv L FR) (hrx5_RB x25519 gv L FR)).
