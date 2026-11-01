(* law consume_response_any, phase Q3: statements 12..13 of P6's
   then-branch: target = NULL; if (ia.ok) { the first table entry with the receiver index; if a handshake entry: the
   node whose peer's entry it is; snapshot state CREATED_INITIATION: before = the snapshot's ck / hash,
   m_consume_response(&st, &before, ...) -> target = p }.  Port of v1's hcr5_Q3.v; hcr5_Q3_ok applies hcr5_q3_all.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q3_pure.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_q3_sep.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope Z_scope.

#[local] Instance hcr5_q3_cceH : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.
#[local] Instance hcr5_q3_cceK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.
#[local] Instance hcr5_q3_cceN : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

Lemma hcr5_q3_mident_cs sh I p : @data_at HCS sh t_mident (mident_val I) p =
  @data_at W_consume_response_any sh t_mident
    (bytes (mi_priv I), (bytes (mi_pub I), Vint (if mi_ok I then Int.one else Int.zero))) p.
Proof. set (v := mident_val I). rewrite (@data_at_change_composite HCS W_consume_response_any _ sh t_mident v v (JMeq_refl _)); [reflexivity | prove_cs_preserve_type]. Qed.
(* ---------------------------------------------------------------------- *)
(* Helpers: compspecs conversions, an entry of the pool                    *)
(* ---------------------------------------------------------------------- *)

Lemma hcr5_q3_conv_itab sh (v: val) p :
  @data_at Noise.CS sh t_itab v p = @data_at W_consume_response_any sh t_itab v p.
Proof. rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_itab v v (JMeq_refl v)); [reflexivity | prove_cs_preserve_type]. Qed.

Lemma hcr5_q3_conv_entry sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p =
  @data_at W_consume_response_any sh t_entry_s (entry_val E n h) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_entry_s (entry_val E n h) (entry_val E n h) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q3_conv_resp sh M p :
  @data_at Noise.CS sh t_resp (resp_val M) p =
  @data_at W_consume_response_any sh t_resp (resp_val M) p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh t_resp (resp_val M) (resp_val M) (JMeq_refl _));
    [reflexivity | prove_cs_preserve_type].
Qed.

Lemma hcr5_q3_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hcr5_q3_iter_split L D1 x D2 :
  iter_sepcon (pool_item_rep L) (D1 ++ x :: D2) =
  (pool_item_rep L x * iter_sepcon (pool_item_rep L) (D1 ++ D2))%logic.
Proof.
  rewrite !iter_sepcon_app. simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

Lemma hcr5_q3_valid L D a :
  In a (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  iter_sepcon (pool_item_rep L) D |-- valid_pointer a.
Proof.
  intros Ha HF. destruct (hcr5_q3_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hcr5_q3_iter_split. apply sepcon_valid_pointer1.
  unfold pool_item_rep, entry_at. apply data_at_valid_ptr; [| simpl; lia].
  rewrite Forall_forall in HF. specialize (HF (a, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
  apply readable_nonidentity, writable_readable; exact HF.
Qed.

Lemma hcr5_q3_isptr L D a :
  In a (saddrs D) -> iter_sepcon (pool_item_rep L) D |-- !! isptr a.
Proof.
  intros Ha. destruct (hcr5_q3_split D a Ha) as (D1 & sh & E & D2 & ->).
  rewrite hcr5_q3_iter_split. unfold pool_item_rep, entry_at. entailer!. destruct H; auto.
Qed.

Lemma hcr5_q3_ptrs L D : iter_sepcon (pool_item_rep L) D |-- !! Forall isptr (saddrs D).
Proof.
  induction D as [| [[a sh] E] D IH]; [simpl; entailer! |].
  change (iter_sepcon (pool_item_rep L) ((a, sh, E) :: D)) with (pool_item_rep L (a, sh, E) * iter_sepcon (pool_item_rep L) D)%logic.
  rewrite (add_andp _ _ IH). unfold pool_item_rep at 1, entry_at. unfold saddrs; cbn [map]; fold (saddrs D).
  entailer!. all: try (constructor; auto); match goal with Hf: field_compatible _ _ _ |- _ => destruct Hf; auto end.
Qed.

Lemma hcr5_q3_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_consume_response_any sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hcr5_q3_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite hcr5_q3_iter_split. unfold pool_item_rep, entry_at. rewrite hcr5_q3_conv_entry. reflexivity.
Qed.

Lemma hcr5_q3_succ_in L a : succ_in L a <> nullval -> In (succ_in L a) L.
Proof.
  induction L as [| x L IH]; simpl; intros H; [congruence |].
  destruct (EqDec_val x a).
  - destruct L; simpl in *; [congruence | auto].
  - right. auto.
Qed.

Lemma hcr5_q3_succ_pn L a : (forall x, In x L -> isptr x) -> is_pointer_or_null (succ_in L a).
Proof.
  intros HL. destruct (eq_dec (succ_in L a) nullval) as [-> | Hn]; [simpl; auto |].
  specialize (HL _ (hcr5_q3_succ_in L a Hn)). destruct (succ_in L a); try contradiction; simpl; auto.
Qed.

Lemma hcr5_q3_find_app T L1 L2 idx :
  t_find_index T (L1 ++ L2) idx =
  match t_find_index T L1 idx with None => t_find_index T L2 idx | r => r end.
Proof.
  induction L1 as [| a L1 IH]; simpl; [reflexivity |].
  destruct (t_entry T a) as [E |]; [destruct (Int.eq (e_index E) idx) |]; auto.
Qed.

Lemma hcr5_q3_succ_mid L1 a L2 : NoDup (L1 ++ a :: L2) -> succ_in (L1 ++ a :: L2) a = hd nullval L2.
Proof.
  induction L1 as [| x L1 IH]; simpl; intros Hnd.
  - destruct (EqDec_val a a); [reflexivity | congruence].
  - inversion Hnd as [| ? ? Hni Hnd']; subst. destruct (EqDec_val x a) as [-> | Hne].
    + exfalso. apply Hni. apply in_or_app. right. left. reflexivity.
    + apply IH. exact Hnd'.
Qed.

Lemma hcr5_q3_lm_snoc l N e :
  hcr5_q3_lm (l ++ [N]) e = if eq_dec (hs_addr (hn_p N)) e then hn_addr N else hcr5_q3_lm l e.
Proof. unfold hcr5_q3_lm. rewrite fold_left_app. reflexivity. Qed.

Lemma hcr5_q3_off48 x : isptr x -> offset_val 0 (offset_val 48 x) = hs_addr x.
Proof.
  intros Hx. destruct x; try contradiction. unfold hs_addr, OFS_PEER_HANDSHAKE. simpl.
  rewrite Ptrofs.add_zero. reflexivity.
Qed.

Lemma hcr5_q3_wand1 (A Q: mpred) : (A * (A -* Q) |-- Q)%logic.
Proof. apply wand_frame_elim. Qed.

Lemma hcr5_q3_sn_hs T a E H : sn_hs (snap_of T a E H) = H.
Proof. reflexivity. Qed.

Lemma hcr5_q3_split_T bs p : hbytes Tsh bs p |-- (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.
Lemma hcr5_q3_join_T bs p : (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic |-- hbytes Tsh bs p.
Proof. unfold hbytes. rewrite (data_at_share_join Ews (Share.comp Ews) Tsh); [apply derives_refl | apply join_comp_Tsh]. Qed.

Lemma hcr5_q3_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros Hs. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

Lemma hcr5_q3_entry_next E n h :
  (let (x, _) := let (_, y) := entry_val E n h in y in x) = n.
Proof. reflexivity. Qed.

Lemma hcr5_q3_sfind_mid {A: Type} (D1 D2: list (val * share * A)) a sh E :
  NoDup (saddrs (D1 ++ (a, sh, E) :: D2)) -> sfind (D1 ++ (a, sh, E) :: D2) a = Some (sh, E).
Proof.
  induction D1 as [| [[x shx] Ex] D1 IH]; simpl; intros Hnd.
  - destruct (EqDec_val a a); [reflexivity | congruence].
  - inversion Hnd as [| ? ? Hni Hnd']; subst. destruct (EqDec_val x a) as [-> | Hne].
    + exfalso. apply Hni. unfold saddrs. rewrite map_app. apply in_or_app. right. left. reflexivity.
    + apply IH. exact Hnd'.
Qed.

Lemma hcr5_q3_focus2 L D e :
  In e (saddrs D) -> NoDup (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\ sfind D e = Some (sh, E) /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_consume_response_any sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha Hnd HF. destruct (hcr5_q3_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split; [| split].
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - apply hcr5_q3_sfind_mid; exact Hnd.
  - rewrite hcr5_q3_iter_split. unfold pool_item_rep, entry_at. rewrite hcr5_q3_conv_entry. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* Q3 cut by hand: the statement's pieces                                  *)
(* ---------------------------------------------------------------------- *)

(* Q3 = target = NULL; t'86 = ia.ok; if (t'86) THEN *)
Definition hcr5_q3_s0 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_Q3] in
  (match hcr5_Q3 with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hcr5_q3_s86 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_Q3] in
  (match hcr5_Q3 with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_c86 : expr := ltac:(let x := eval cbv beta iota delta [hcr5_Q3] in
  (match hcr5_Q3 with Ssequence _ (Ssequence _ (Sifthenelse c _ _)) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hcr5_q3_THEN : statement := ltac:(let x := eval cbv beta iota delta [hcr5_Q3] in
  (match hcr5_Q3 with Ssequence _ (Ssequence _ (Sifthenelse _ t _)) => t | _ => Sskip end) in exact x).
(* THEN = (e = ita.head; for (;;) B1 I1); if24; if (t'24) HS *)
Definition hcr5_q3_se : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence (Ssequence s _) _ => s | _ => Sskip end) in exact x).
Definition hcr5_q3_B1 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence (Ssequence _ (Sloop b _)) _ => b | _ => Sskip end) in exact x).
Definition hcr5_q3_I1 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence (Ssequence _ (Sloop _ i)) _ => i | _ => Sskip end) in exact x).
Definition hcr5_q3_if24 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_c24 : expr := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence _ (Ssequence _ (Sifthenelse c _ _)) => c | _ => Econst_int Int.zero tint end) in exact x).
Definition hcr5_q3_HS : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_THEN] in
  (match hcr5_q3_THEN with Ssequence _ (Ssequence _ (Sifthenelse _ t _)) => t | _ => Sskip end) in exact x).
(* HS = p = NULL; (it = peers; for (;;) B2 I2); if23; if (t'23) CALL *)
Definition hcr5_q3_sp : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hcr5_q3_sit : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence (Ssequence s _) _) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_B2 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence (Ssequence _ (Sloop b _)) _) => b | _ => Sskip end) in exact x).
Definition hcr5_q3_I2 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence (Ssequence _ (Sloop _ i)) _) => i | _ => Sskip end) in exact x).
Definition hcr5_q3_if23 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_c23 : expr := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence _ (Ssequence _ (Sifthenelse c _ _))) => c
   | _ => Econst_int Int.zero tint end) in exact x).
Definition hcr5_q3_CALL : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_HS] in
  (match hcr5_q3_HS with Ssequence _ (Ssequence _ (Ssequence _ (Sifthenelse _ t _))) => t | _ => Sskip end) in exact x).

Lemma hcr5_q3_eq : hcr5_Q3 = Ssequence hcr5_q3_s0 (Ssequence hcr5_q3_s86 (Sifthenelse hcr5_q3_c86 hcr5_q3_THEN Sskip)).
Proof. reflexivity. Qed.
Lemma hcr5_q3_then_eq : hcr5_q3_THEN =
  Ssequence (Ssequence hcr5_q3_se (Sloop hcr5_q3_B1 hcr5_q3_I1))
    (Ssequence hcr5_q3_if24 (Sifthenelse hcr5_q3_c24 hcr5_q3_HS Sskip)).
Proof. reflexivity. Qed.
Lemma hcr5_q3_hs_eq : hcr5_q3_HS =
  Ssequence hcr5_q3_sp (Ssequence (Ssequence hcr5_q3_sit (Sloop hcr5_q3_B2 hcr5_q3_I2))
    (Ssequence hcr5_q3_if23 (Sifthenelse hcr5_q3_c23 hcr5_q3_CALL Sskip))).
Proof. reflexivity. Qed.

Lemma hcr5_q3_post {Espec: OracleKind} {cs: compspecs} Delta P c (Q Q': environ -> mpred) R :
  ENTAIL Delta, Q |-- Q' -> semax Delta P c (overridePost Q R) -> semax Delta P c (overridePost Q' R).
Proof.
  intros HE Hs. eapply semax_post; [| | | | exact Hs]; destruct R; simpl; auto;
    intros; apply andp_left2, derives_refl.
Qed.

Ltac hcr5_q3_vp := first [ apply hcr5_q3_valid; solve [auto]
                         | apply sepcon_valid_pointer2; hcr5_q3_vp
                         | apply sepcon_valid_pointer1; hcr5_q3_vp ].

Section Q3.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Local Notation D3 := (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec).

(* the locals of the block (target is listed apart) *)
Definition hcr5_q3_Q gv L (kes m h0 ret: val) : list localdef :=
  [temp HR5._kes kes; temp HR5._msg m; temp HR5._head0 h0; temp HR5._ret ret] ++ hcr5_lvars gv L.

(* the SEP items the block reads, then an opaque frame FX (the rest of SQ2) *)
Definition hcr5_q3_R gv L IA NS NSs T m M (st: mpred) FX : list mpred :=
  [@data_at HCS Tsh t_mident (mident_val IA) (l_ia L); itable Tsh (l_ita L) T;
   @data_at W Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L); hnodes_rep4 W (hcr5_head NS) NSs;
   resp_rep Ews m M; wg_consts gv; st; @data_at_ HCS Tsh t_mstate (l_before L); FX].

(* the then-branch's start (ia.ok) *)
Definition hcr5_q3_A0 gv L IA NS NSs T m M kes h0 ret FX : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* the table walk's result *)
Definition hcr5_q3_ef (T: tstate) (idx: int) : val :=
  match t_find_index T (t_L T) idx with None => nullval | Some (a, _) => a end.

Definition hcr5_q3_A1 gv L IA NS NSs T m M kes h0 ret FX : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._e (hcr5_q3_ef T (rm_receiver M)) :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* a handshake entry a was found: the node walk's start *)
Definition hcr5_q3_A3 gv L IA NS NSs T m M kes h0 ret FX (a: val) : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._e a :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* after the node walk: p = the node of the entry's peer *)
Definition hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX (a p: val) : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._p p :: temp HR5._e a :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* the end of the block *)
Definition hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._target (hcr5_tnode NS (hcr5_tgt x25519 aead_dec IA T PS M)) :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (hcr5_st_rep (hcr5_tgt x25519 aead_dec IA T PS M) (l_st L)) FX))).

(* ---- the table walk: for (; e && e->index != msg->receiver_index; e = e->next); ---- *)
Definition hcr5_q3_WI gv L T m M kes h0 ret (F: mpred) (L1 L2: list val) : environ -> mpred :=
  PROPx [t_L T = L1 ++ L2; t_find_index T L1 (rm_receiver M) = None]
  (LOCALx (temp HR5._e (hd nullval L2) :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_WC gv L T m M kes h0 ret (F: mpred) (L1: list val) (a: val) (L2: list val) : environ -> mpred :=
  PROPx [t_L T = L1 ++ a :: L2; t_find_index T (L1 ++ [a]) (rm_receiver M) = None]
  (LOCALx (temp HR5._e a :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_WB gv L T m M kes h0 ret (F: mpred) : environ -> mpred :=
  PROPx []
  (LOCALx (temp HR5._e (hcr5_q3_ef T (rm_receiver M)) :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [@data_at W Ews t_resp (resp_val M) m; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_WIx gv L T m M kes h0 ret (F: mpred) : environ -> mpred :=
  EX L1: list val, EX L2: list val, hcr5_q3_WI gv L T m M kes h0 ret F L1 L2.
Definition hcr5_q3_WCx gv L T m M kes h0 ret (F: mpred) : environ -> mpred :=
  EX L1: list val, EX a: val, EX L2: list val, hcr5_q3_WC gv L T m M kes h0 ret F L1 a L2.

Lemma hcr5_q3_Lb_nil {Espec: OracleKind} gv L T m M kes h0 ret F L1 Rr :
  semax D3 (hcr5_q3_WI gv L T m M kes h0 ret F L1 []) hcr5_q3_B1
    (loop1_ret_assert (hcr5_q3_WCx gv L T m M kes h0 ret F) (overridePost (hcr5_q3_WB gv L T m M kes h0 ret F) Rr)).
Proof.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hcr5_q3_WI, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_B1. cbn [app hd]. simplify_func_tycontext.
  Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'19 (Vint Int.zero) :: Q) (SEPx Rs))) end.
  { exfalso. congruence. }
  { forward. entailer!. }
  forward_if; [exfalso; congruence |].
  forward.
  unfold hcr5_q3_WB, hcr5_q3_Q, hcr5_lvars. cbn [app]. entailer!. unfold hcr5_q3_ef.
  match goal with Hl: t_L T = L1 ++ [], Hf: t_find_index T L1 _ = None |- _ =>
    rewrite Hl, app_nil_r, Hf end. reflexivity.
Qed.

Lemma hcr5_q3_Lb_cons {Espec: OracleKind} gv L T m M kes h0 ret F L1 a L2 Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D3 (hcr5_q3_WI gv L T m M kes h0 ret F L1 (a :: L2)) hcr5_q3_B1
    (loop1_ret_assert (hcr5_q3_WCx gv L T m M kes h0 ret F) (overridePost (hcr5_q3_WB gv L T m M kes h0 ret F) Rr)).
Proof.
  intros Hwf HLp. destruct Hwf as (HwL & HwI & HwD & HwS).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hcr5_q3_WI, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_B1. cbn [app hd]. simplify_func_tycontext.
  Intros.
  assert (Ha: In a (t_L T)).
  { match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rewrite Hl end. apply in_or_app; right; left; reflexivity. }
  destruct (hcr5_q3_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E & Rst & Hrd & Hsf & Heq).
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'19 (Vint (if Int.eq (e_index E) (rm_receiver M) then Int.zero else Int.one)) :: Q) (SEPx Rs))) end.
  { forward. forward. forward. entailer!. destruct (Int.eq (e_index E) (rm_receiver M)); reflexivity. }
  { exfalso. specialize (HLp a Ha). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq.
  assert (Hfa: t_find_index T (L1 ++ [a]) (rm_receiver M) =
               if Int.eq (e_index E) (rm_receiver M) then Some (a, E) else None).
  { match goal with Hf: t_find_index T L1 _ = None |- _ => rewrite hcr5_q3_find_app, Hf end.
    simpl. unfold t_entry. rewrite Hsf. destruct (Int.eq (e_index E) (rm_receiver M)); reflexivity. }
  forward_if.
  - forward.
    unfold hcr5_q3_WCx, hcr5_q3_WC, hcr5_q3_Q, hcr5_lvars. cbn [app]. Exists L1 a L2. entailer!.
    rewrite Hfa. destruct (Int.eq (e_index E) (rm_receiver M)); [exfalso | reflexivity].
    match goal with Hn: Int.repr 0 <> Int.zero |- _ => apply Hn; reflexivity end.
  - forward.
    unfold hcr5_q3_WB, hcr5_q3_Q, hcr5_lvars. cbn [app]. entailer!. unfold hcr5_q3_ef.
    match goal with Hl: t_L T = L1 ++ a :: L2, Hf: t_find_index T L1 _ = None |- _ =>
      rewrite Hl, hcr5_q3_find_app, Hf end.
    simpl. unfold t_entry. rewrite Hsf.
    destruct (Int.eq (e_index E) (rm_receiver M)); [reflexivity | exfalso].
    match goal with Hn: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hn) end.
Qed.

Lemma hcr5_q3_Li {Espec: OracleKind} gv L T m M kes h0 ret F L1 a L2 Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D3 (hcr5_q3_WC gv L T m M kes h0 ret F L1 a L2) hcr5_q3_I1
    (loop2_ret_assert (hcr5_q3_WIx gv L T m M kes h0 ret F) (overridePost (hcr5_q3_WB gv L T m M kes h0 ret F) Rr)).
Proof.
  intros Hwf HLp. destruct Hwf as (HwL & HwI & HwD & HwS).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop2_ret_assert].
  unfold hcr5_q3_WC, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_I1. cbn [app]. simplify_func_tycontext.
  Intros.
  assert (Ha: In a (t_L T)).
  { match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rewrite Hl end. apply in_or_app; right; left; reflexivity. }
  destruct (hcr5_q3_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E & Rst & Hrd & Hsf & Heq).
  rewrite Heq. Intros. forward.
  { entailer!. unfold entry_val. apply hcr5_q3_succ_pn; auto. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq.
  unfold hcr5_q3_WIx, hcr5_q3_WI, hcr5_q3_Q, hcr5_lvars. cbn [app].
  Exists (L1 ++ [a]) L2. entailer!.
  match goal with Hl: t_L T = L1 ++ a :: L2 |- _ => rename Hl into HL1 end. split.
  - rewrite HL1, <- app_assoc. reflexivity.
  - rewrite hcr5_q3_entry_next. rewrite HL1 in HwL |- *. symmetry. apply hcr5_q3_succ_mid; auto.
Qed.

Lemma hcr5_q3_Lloop {Espec: OracleKind} gv L T m M kes h0 ret F Rr :
  itable_wf T -> (forall a, In a (t_L T) -> isptr a) ->
  semax D3 (hcr5_q3_WI gv L T m M kes h0 ret F [] (t_L T)) (Sloop hcr5_q3_B1 hcr5_q3_I1)
    (overridePost (hcr5_q3_WB gv L T m M kes h0 ret F) Rr).
Proof.
  intros Hwf HLp.
  eapply semax_pre with (P' := hcr5_q3_WIx gv L T m M kes h0 ret F).
  { unfold hcr5_q3_WIx. apply andp_left2. Exists (@nil val) (t_L T). apply derives_refl. }
  apply semax_loop with (Q' := hcr5_q3_WCx gv L T m M kes h0 ret F).
  - unfold hcr5_q3_WIx at 1. apply semax_extract_exists; intro L1. apply semax_extract_exists; intro L2.
    destruct L2 as [| a L2]; [apply hcr5_q3_Lb_nil | apply hcr5_q3_Lb_cons; assumption].
  - unfold hcr5_q3_WCx at 1. apply semax_extract_exists; intro L1. apply semax_extract_exists; intro a.
    apply semax_extract_exists; intro L2. apply hcr5_q3_Li; assumption.
Qed.

(* e = ita.head; for (; e && e->index != msg->receiver_index; e = e->next); *)
Lemma hcr5_q3_Lwalk {Espec: OracleKind} gv L IA NS NSs T m M kes h0 ret FX Rr :
  semax D3 (hcr5_q3_A0 gv L IA NS NSs T m M kes h0 ret FX)
    (Ssequence hcr5_q3_se (Sloop hcr5_q3_B1 hcr5_q3_I1))
    (overridePost (hcr5_q3_A1 gv L IA NS NSs T m M kes h0 ret FX) Rr).
Proof.
  unfold hcr5_q3_A0, hcr5_q3_R, hcr5_q3_Q, hcr5_Delta, hcr5_q3_se.
  simplify_func_tycontext. unfold hcr5_lvars; cbn [app].
  unfold itable, resp_rep. Intros. rewrite hcr5_q3_conv_itab, hcr5_q3_conv_resp.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hcr5_q3_ptrs (t_L T) (t_D T)). entailer!. }
  assert (HLp: forall a, In a (t_L T) -> isptr a).
  { intros a Ha. rewrite Forall_forall in Hptr. apply Hptr, HwI, Ha. }
  forward.
  { entailer!. destruct (t_L T) as [| a0 L'] eqn:HL; simpl; auto.
    specialize (HLp a0 (or_introl eq_refl)). destruct a0; try contradiction; simpl; auto. }
  freeze FZ := - (data_at _ t_resp _ m) (iter_sepcon _ _).
  eapply semax_pre; [| eapply hcr5_q3_post; [| apply (hcr5_q3_Lloop gv L T m M kes h0 ret (FRZL FZ)); assumption]].
  - unfold hcr5_q3_WI, hcr5_q3_Q, hcr5_lvars; cbn [app hd]. entailer!.
  - unfold hcr5_q3_WB, hcr5_q3_A1, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars; cbn [app].
    thaw FZ. rewrite <- hcr5_q3_conv_resp, <- hcr5_q3_conv_itab. unfold itable, resp_rep.
    entailer!.
Qed.

(* ---- if (e != NULL && e->type == INDEX_HASHTABLE_HANDSHAKE) HS ---- *)
(* not found *)
Lemma hcr5_q3_Lnf {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = None ->
  semax D3 (hcr5_q3_A1 gv L IA NS NSs T m M kes h0 ret FX)
    (Ssequence hcr5_q3_if24 (Sifthenelse hcr5_q3_c24 hcr5_q3_HS Sskip))
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros Hok Hfind.
  assert (Htg: hcr5_tgt x25519 aead_dec IA T PS M = None) by (unfold hcr5_tgt; rewrite Hok, Hfind; reflexivity).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_A1, hcr5_q3_ef. rewrite Hfind.
  unfold hcr5_q3_R, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_if24, hcr5_q3_c24. cbn [app]. simplify_func_tycontext.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'22 (Vint Int.zero) :: Q) (SEPx Rs))) end.
  { exfalso. discriminate. }
  { forward. entailer!. }
  forward_if; [exfalso; congruence |].
  forward.
  unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite Htg. cbn [hcr5_tnode hcr5_st_rep app].
  entailer!.
Qed.

(* found, not a handshake entry *)
Lemma hcr5_q3_Lnhs {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX Rr a E :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = false ->
  semax D3 (hcr5_q3_A1 gv L IA NS NSs T m M kes h0 ret FX)
    (Ssequence hcr5_q3_if24 (Sifthenelse hcr5_q3_c24 hcr5_q3_HS Sskip))
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros Hok Hfind Hty.
  assert (Htg: hcr5_tgt x25519 aead_dec IA T PS M = None)
    by (unfold hcr5_tgt; rewrite Hok, Hfind, Hty; reflexivity).
  destruct hcr5_q3_pure_ok as (Pfind & _).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_A1, hcr5_q3_ef. rewrite Hfind.
  unfold hcr5_q3_R, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_if24, hcr5_q3_c24. cbn [app]. simplify_func_tycontext.
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hcr5_q3_ptrs (t_L T) (t_D T)). entailer!. }
  destruct (hcr5_q3_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E' & Rst & Hrd & Hsf & Heq).
  assert (E' = E) as ->. { unfold t_entry in HtE. rewrite Hsf in HtE. congruence. }
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'22 (Vint (if Int.eq (e_type E) IDX_HANDSHAKE then Int.one else Int.zero)) :: Q) (SEPx Rs))) end.
  { forward. forward. entailer!. unfold IDX_HANDSHAKE. destruct (Int.eq (e_type E) (Int.repr 1)); reflexivity. }
  { exfalso. rewrite Forall_forall in Hptr. specialize (Hptr a (HwI _ Ha)). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq. rewrite Hty.
  forward_if; [exfalso; congruence |].
  forward.
  unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars, itable. rewrite Htg. cbn [hcr5_tnode hcr5_st_rep app].
  entailer!.
Qed.

(* found, a handshake entry: HS *)
Lemma hcr5_q3_Lhs {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX Rr a E :
  t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true ->
  semax D3 (hcr5_q3_A3 gv L IA NS NSs T m M kes h0 ret FX a) hcr5_q3_HS
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr) ->
  semax D3 (hcr5_q3_A1 gv L IA NS NSs T m M kes h0 ret FX)
    (Ssequence hcr5_q3_if24 (Sifthenelse hcr5_q3_c24 hcr5_q3_HS Sskip))
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros Hfind Hty HHS.
  destruct hcr5_q3_pure_ok as (Pfind & _).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost] in HHS |- *.
  unfold hcr5_q3_A1, hcr5_q3_ef. rewrite Hfind.
  unfold hcr5_q3_R, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_if24, hcr5_q3_c24. cbn [app].
  unfold hcr5_Delta in HHS. simplify_func_tycontext.
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr. { sep_apply (hcr5_q3_ptrs (t_L T) (t_D T)). entailer!. }
  destruct (hcr5_q3_focus2 (t_L T) (t_D T) a (HwI _ Ha) HwD HwS) as (sh & E' & Rst & Hrd & Hsf & Heq).
  assert (E' = E) as ->. { unfold t_entry in HtE. rewrite Hsf in HtE. congruence. }
  rewrite Heq. Intros.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._t'22 (Vint (if Int.eq (e_type E) IDX_HANDSHAKE then Int.one else Int.zero)) :: Q) (SEPx Rs))) end.
  { forward. forward. entailer!. unfold IDX_HANDSHAKE. destruct (Int.eq (e_type E) (Int.repr 1)); reflexivity. }
  { exfalso. rewrite Forall_forall in Hptr. specialize (Hptr a (HwI _ Ha)). destruct a; try contradiction. discriminate. }
  gather_SEP (data_at sh t_entry_s _ a) Rst. rewrite <- Heq. rewrite Hty.
  forward_if.
  2: { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
  eapply semax_pre; [| exact HHS].
  unfold hcr5_q3_A3, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars, itable; cbn [app].
  entailer!.
Qed.

(* ---- HS: p = NULL; for (it = peers; it; it = it->next) if (&it->p->handshake.entry == e) p = it; ---- *)
Lemma hcr5_q3_Lsp {Espec: OracleKind} gv L IA NS NSs T m M kes h0 ret FX a Rr :
  semax D3 (hcr5_q3_A3 gv L IA NS NSs T m M kes h0 ret FX a) hcr5_q3_sp
    (overridePost (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a nullval) Rr).
Proof.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_A3, hcr5_q3_A4, hcr5_Delta, hcr5_q3_sp. simplify_func_tycontext.
  forward. apply ENTAIL_refl.
Qed.

Definition hcr5_q3_NI gv L T m kes h0 ret (F: mpred) (NSs: list hnode4) (a: val) (NS1 NS2: list hnode4) : environ -> mpred :=
  PROPx [NSs = NS1 ++ NS2]
  (LOCALx (temp HR5._it (hcr5_head NS2) :: temp HR5._p (hcr5_q3_lm NS1 a) :: temp HR5._e a :: temp HR5._target nullval ::
           hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [hnodes_rep4 W (hcr5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_NC gv L T m kes h0 ret (F: mpred) (NSs: list hnode4) (a: val) (NS1: list hnode4) (N: hnode4)
  (NS2: list hnode4) : environ -> mpred :=
  PROPx [NSs = NS1 ++ N :: NS2]
  (LOCALx (temp HR5._it (hn_addr N) :: temp HR5._p (hcr5_q3_lm (NS1 ++ [N]) a) :: temp HR5._e a ::
           temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [hnodes_rep4 W (hcr5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_NB gv L T m kes h0 ret (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  PROPx []
  (LOCALx (temp HR5._it nullval :: temp HR5._p (hcr5_q3_lm NSs a) :: temp HR5._e a :: temp HR5._target nullval ::
           hcr5_q3_Q gv L kes m h0 ret)
  (SEPx [hnodes_rep4 W (hcr5_head NSs) NSs; iter_sepcon (pool_item_rep (t_L T)) (t_D T); F])).
Definition hcr5_q3_NIx gv L T m kes h0 ret (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  EX NS1: list hnode4, EX NS2: list hnode4, hcr5_q3_NI gv L T m kes h0 ret F NSs a NS1 NS2.
Definition hcr5_q3_NCx gv L T m kes h0 ret (F: mpred) (NSs: list hnode4) (a: val) : environ -> mpred :=
  EX NS1: list hnode4, EX N: hnode4, EX NS2: list hnode4, hcr5_q3_NC gv L T m kes h0 ret F NSs a NS1 N NS2.

Lemma hcr5_q3_Nb_nil {Espec: OracleKind} gv L T m kes h0 ret F NSs a NS1 Rr :
  semax D3 (hcr5_q3_NI gv L T m kes h0 ret F NSs a NS1 []) hcr5_q3_B2
    (loop1_ret_assert (hcr5_q3_NCx gv L T m kes h0 ret F NSs a) (overridePost (hcr5_q3_NB gv L T m kes h0 ret F NSs a) Rr)).
Proof.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hcr5_q3_NI, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_B2. cbn [app hcr5_head]. simplify_func_tycontext.
  Intros.
  forward_if.
  - exfalso. match goal with Hc: isptr (Vlong _) |- _ => exact Hc end.
  - forward. unfold hcr5_q3_NB, hcr5_q3_Q, hcr5_lvars. cbn [app].
    match goal with Hl: NSs = NS1 ++ [] |- _ => rewrite app_nil_r in Hl; rewrite <- Hl end.
    entailer!.
Qed.

Lemma hcr5_q3_Nb_cons {Espec: OracleKind} gv L T m kes h0 ret F NSs a NS1 N NS2 Rr :
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) (t_D T) ->
  In a (saddrs (t_D T)) -> Forall isptr (map hn_addr NSs) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D3 (hcr5_q3_NI gv L T m kes h0 ret F NSs a NS1 (N :: NS2)) hcr5_q3_B2
    (loop1_ret_assert (hcr5_q3_NCx gv L T m kes h0 ret F NSs a) (overridePost (hcr5_q3_NB gv L T m kes h0 ret F NSs a) Rr)).
Proof.
  intros Hwr Ha HptrN HfcP.
  destruct hcr5_q3_sep_ok as (Snode & _ & Svalid & _).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop1_ret_assert].
  unfold hcr5_q3_NI, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_B2. cbn [app hcr5_head]. simplify_func_tycontext.
  Intros. match goal with Hl: NSs = NS1 ++ N :: NS2 |- _ => rename Hl into HNS end.
  assert (HinN: In (hn_addr N) (map hn_addr NSs)).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  assert (HpN: isptr (hn_addr N)) by (rewrite Forall_forall in HptrN; auto).
  forward_if.
  2: { exfalso. match goal with Hc: _ = nullval |- _ => change (hn_addr N = nullval) in Hc; rewrite Hc in HpN; exact HpN end. }
  assert (Hnode: hnodes_rep4 W (hcr5_head NSs) NSs |--
    (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N) -*
      hnodes_rep4 W (hcr5_head NSs) NSs))%logic).
  { rewrite HNS. apply Snode. }
  assert (HinPN: In (hn_p N) (map hn_p NSs)).
  { rewrite HNS, map_app. apply in_or_app. right. left. reflexivity. }
  destruct (HfcP _ HinPN) as [HfcN HpoolN].
  assert (HpPN: isptr (hn_p N)) by (destruct HfcN as [? _]; assumption).
  sep_apply Hnode. Intros.
  forward.
  lazymatch goal with |- semax _ (PROPx ?P (LOCALx (_ :: _ :: _ :: ?Q) (SEPx ?Rs))) _ _ =>
    forward_if (PROPx P (LOCALx (temp HR5._it (hn_addr N) :: temp HR5._p (hcr5_q3_lm (NS1 ++ [N]) a) :: Q) (SEPx Rs))) end.
  { apply denote_tc_test_eq_split; hcr5_q3_vp. }
  { match goal with Hc: offset_val 0 (offset_val 48 (hn_p N)) = a |- _ =>
      rewrite hcr5_q3_off48 in Hc by exact HpPN; rename Hc into Heqa end.
    forward. entailer!. rewrite hcr5_q3_lm_snoc.
    match goal with |- context [eq_dec ?x ?y] => destruct (eq_dec x y) end; [reflexivity | congruence]. }
  { match goal with Hc: offset_val 0 (offset_val 48 (hn_p N)) <> a |- _ =>
      rewrite hcr5_q3_off48 in Hc by exact HpPN; rename Hc into Hnea end.
    forward. entailer!. rewrite hcr5_q3_lm_snoc.
    match goal with |- context [eq_dec ?x ?y] => destruct (eq_dec x y) end; [contradiction | reflexivity]. }
  sep_apply (hcr5_q3_wand1 (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N))
               (hnodes_rep4 W (hcr5_head NSs) NSs)).
  unfold hcr5_q3_NCx, hcr5_q3_NC, hcr5_q3_Q, hcr5_lvars. cbn [app].
  Exists NS1 N NS2. entailer!.
Qed.

Lemma hcr5_q3_Ni {Espec: OracleKind} gv L T m kes h0 ret F NSs a NS1 N NS2 Rr :
  Forall isptr (map hn_addr NSs) ->
  semax D3 (hcr5_q3_NC gv L T m kes h0 ret F NSs a NS1 N NS2) hcr5_q3_I2
    (loop2_ret_assert (hcr5_q3_NIx gv L T m kes h0 ret F NSs a) (overridePost (hcr5_q3_NB gv L T m kes h0 ret F NSs a) Rr)).
Proof.
  intros HptrN.
  destruct hcr5_q3_sep_ok as (Snode & _).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost loop2_ret_assert].
  unfold hcr5_q3_NC, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_I2. cbn [app]. simplify_func_tycontext.
  Intros. match goal with Hl: NSs = NS1 ++ N :: NS2 |- _ => rename Hl into HNS end.
  assert (Hnode: hnodes_rep4 W (hcr5_head NSs) NSs |--
    (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N) *
     (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N) -*
      hnodes_rep4 W (hcr5_head NSs) NSs))%logic).
  { rewrite HNS. apply Snode. }
  assert (HnxP: is_pointer_or_null (hcr5_head NS2)).
  { destruct NS2 as [| N2 NS2]; simpl; auto.
    assert (Hin2: In (hn_addr N2) (map hn_addr NSs)).
    { rewrite HNS, map_app. apply in_or_app. right. right. left. reflexivity. }
    rewrite Forall_forall in HptrN. specialize (HptrN _ Hin2). destruct (hn_addr N2); try contradiction; simpl; auto. }
  sep_apply Hnode. Intros.
  forward.
  sep_apply (hcr5_q3_wand1 (@data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, hcr5_head NS2)))) (hn_addr N))
               (hnodes_rep4 W (hcr5_head NSs) NSs)).
  unfold hcr5_q3_NIx, hcr5_q3_NI, hcr5_q3_Q, hcr5_lvars. cbn [app].
  Exists (NS1 ++ [N]) NS2. entailer!. try subst NSs. rewrite <- app_assoc. reflexivity.
Qed.

Lemma hcr5_q3_Nloop {Espec: OracleKind} gv L T m kes h0 ret F NSs a Rr :
  Forall (fun x => match x with (_, sh, _) => writable_share sh end) (t_D T) ->
  In a (saddrs (t_D T)) -> Forall isptr (map hn_addr NSs) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D3 (hcr5_q3_NI gv L T m kes h0 ret F NSs a [] NSs) (Sloop hcr5_q3_B2 hcr5_q3_I2)
    (overridePost (hcr5_q3_NB gv L T m kes h0 ret F NSs a) Rr).
Proof.
  intros Hwr Ha HptrN HfcP.
  eapply semax_pre with (P' := hcr5_q3_NIx gv L T m kes h0 ret F NSs a).
  { unfold hcr5_q3_NIx. apply andp_left2. Exists (@nil hnode4) NSs. apply derives_refl. }
  apply semax_loop with (Q' := hcr5_q3_NCx gv L T m kes h0 ret F NSs a).
  - unfold hcr5_q3_NIx at 1. apply semax_extract_exists; intro NS1. apply semax_extract_exists; intro NS2.
    destruct NS2 as [| N NS2]; [apply hcr5_q3_Nb_nil | apply hcr5_q3_Nb_cons; assumption].
  - unfold hcr5_q3_NCx at 1. apply semax_extract_exists; intro NS1. apply semax_extract_exists; intro N.
    apply semax_extract_exists; intro NS2. apply hcr5_q3_Ni; assumption.
Qed.

(* it = peers; the node walk *)
Lemma hcr5_q3_Lnode {Espec: OracleKind} gv L IA NS NSs T m M kes h0 ret FX a Rr :
  hcr5_head NSs = hcr5_head NS -> In a (saddrs (t_D T)) ->
  (forall q, In q (map hn_p NSs) -> @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))) ->
  semax D3 (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a nullval)
    (Ssequence hcr5_q3_sit (Sloop hcr5_q3_B2 hcr5_q3_I2))
    (overridePost (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a (hcr5_q3_lm NSs a)) Rr).
Proof.
  intros HsH Ha HfcP.
  destruct hcr5_q3_sep_ok as (_ & _ & _ & Sptrs & _).
  unfold hcr5_q3_A4, hcr5_q3_R, hcr5_q3_Q, hcr5_Delta, hcr5_q3_sit.
  simplify_func_tycontext. unfold hcr5_lvars; cbn [app].
  unfold itable. Intros.
  match goal with Hw: itable_wf T |- _ => pose proof Hw as Hwf; destruct Hw as (HwL & HwI & HwD & HwS) end.
  assert_PROP (Forall isptr (map hn_addr NSs)) as HptrN.
  { sep_apply (Sptrs (hcr5_head NS) NSs). entailer!. }
  forward.
  rewrite <- HsH.
  freeze FZ := - (hnodes_rep4 _ _ _) (iter_sepcon _ _).
  eapply semax_pre; [| eapply hcr5_q3_post; [| apply (hcr5_q3_Nloop gv L T m kes h0 ret (FRZL FZ) NSs a); assumption]].
  - unfold hcr5_q3_NI, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!.
  - unfold hcr5_q3_NB, hcr5_q3_A4, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars; cbn [app].
    thaw FZ. rewrite HsH. unfold itable. entailer!.
Qed.

(* freeze everything but the items K (found by syntactic equality; VST's `freeze F := - a b` unifies the
   patterns with the whole goal and normalizes the SEP list by cbv: minutes on these states) *)
Ltac hcr5_q3_idx R a :=
  lazymatch R with
  | a :: _ => constr:(0%Z)
  | _ :: ?R' => let n := hcr5_q3_idx R' a in constr:(Z.succ n)
  end.
Ltac hcr5_q3_len R :=
  lazymatch R with
  | nil => constr:(O)
  | _ :: ?R' => let n := hcr5_q3_len R' in constr:(S n)
  end.
Ltac hcr5_q3_keep_tac K name :=
  lazymatch goal with |- semax _ (PROPx _ (LOCALx _ (SEPx ?R))) _ _ =>
    let rec idxs l := lazymatch l with
      | nil => constr:(@nil Z)
      | ?a :: ?l' => let i := hcr5_q3_idx R a in let r := idxs l' in constr:(i :: r) end in
    let A := idxs K in
    let n := hcr5_q3_len R in
    let A' := eval compute in (Zlist_complement n A) in
    freeze_tac A' name
  end.
Tactic Notation "hcr5_q3_keep" constr(K) ident(name) := hcr5_q3_keep_tac K name.

(* Opaque atoms for the opened node and the opened message: a term `@data_at W .. t_hnode4 (.., hsnap_val ..)`
   costs a kernel reptype conversion (HCS -> W) at each of its occurrences in a proof term, and the wrappers
   below carry their SEP through many steps; as atoms they cost nothing. *)
Definition hcr5_q3_nodeA (N: hnode4) (nx: val) : mpred :=
  @data_at W Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N).
Definition hcr5_q3_nodeR (N: hnode4) (nx: val) (H: handshake) : mpred :=
  ((hbytes Ews (hs_eph H) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk H) (offset_val 184 (hn_addr N)) *
    hbytes Ews (hs_hash H) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck H) (offset_val 248 (hn_addr N))) -*
   hcr5_q3_nodeA N nx)%logic.
Definition hcr5_q3_respR (M: resp_msg) (m: val) : mpred :=
  ((hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m)) -*
   @data_at W Ews t_resp (resp_val M) m)%logic.

Lemma hcr5_q3_open NSs NSa N0 NSb : NSs = NSa ++ N0 :: NSb ->
  hnodes_rep4 W (hcr5_head NSs) NSs |--
  (hcr5_q3_nodeA N0 (hcr5_head NSb) * (hcr5_q3_nodeA N0 (hcr5_head NSb) -* hnodes_rep4 W (hcr5_head NSs) NSs))%logic.
Proof.
  intros ->. destruct hcr5_q3_sep_ok as (Snode & _). unfold hcr5_q3_nodeA. apply Snode.
Qed.

Lemma hcr5_q3_fields T N nx p P : hn_snap N = hsnap_val (hs_snap_cur T p P) -> hs_ok (p_hs P) ->
  hcr5_q3_nodeA N nx |--
  (hbytes Ews (hs_eph (p_hs P)) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk (p_hs P)) (offset_val 184 (hn_addr N)) *
   hbytes Ews (hs_hash (p_hs P)) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck (p_hs P)) (offset_val 248 (hn_addr N)) *
   hcr5_q3_nodeR N nx (p_hs P))%logic.
Proof.
  intros Hs Hok. destruct hcr5_q3_sep_ok as (_ & Sfields & _).
  unfold hcr5_q3_nodeR, hcr5_q3_nodeA. rewrite Hs.
  exact (Sfields Ews (hn_p N) (hs_snap_cur T p P) (hn_refs N) (hn_rest N) nx (hn_addr N) Hok).
Qed.

Lemma hcr5_q3_unfields N nx H :
  (hbytes Ews (hs_eph H) (offset_val 56 (hn_addr N)) * hbytes Ews (hs_psk H) (offset_val 184 (hn_addr N)) *
   hbytes Ews (hs_hash H) (offset_val 216 (hn_addr N)) * hbytes Ews (hs_ck H) (offset_val 248 (hn_addr N)) *
   hcr5_q3_nodeR N nx H)%logic |-- hcr5_q3_nodeA N nx.
Proof. unfold hcr5_q3_nodeR. apply wand_frame_elim. Qed.

Lemma hcr5_q3_resp_open M m :
  resp_rep Ews m M |--
  (!! rm_ok M && (hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m) *
                  hcr5_q3_respR M m))%logic.
Proof.
  destruct hcr5_q3_sep_ok as (_ & _ & _ & _ & Sresp & _).
  unfold resp_rep. apply derives_extract_prop; intro HM. rewrite hcr5_q3_conv_resp. unfold hcr5_q3_respR.
  apply andp_right; [apply prop_right; exact HM |]. apply Sresp; exact HM.
Qed.

Lemma hcr5_q3_resp_close M m : rm_ok M ->
  (hbytes Ews (rm_eph M) (offset_val 12 m) * hbytes Ews (rm_encn M) (offset_val 44 m) * hcr5_q3_respR M m)%logic
  |-- resp_rep Ews m M.
Proof.
  intros HM. unfold resp_rep. apply andp_right; [apply prop_right; exact HM |].
  rewrite hcr5_q3_conv_resp. unfold hcr5_q3_respR. apply wand_frame_elim.
Qed.

(* ---- if (p != NULL && p->snap.state == HANDSHAKE_CREATED_INITIATION) CALL ----
   Floyd steps run in "core" lemmas over a small SEP (the items they touch and an abstract frame F); the
   wrappers only open / close the node and freeze / thaw (a Floyd step over the opened node is very slow
   at Qed). *)
Definition hcr5_q3_Lp gv L (kes m h0 ret p a: val) : list localdef :=
  temp HR5._p p :: temp HR5._e a :: temp HR5._target nullval :: hcr5_q3_Q gv L kes m h0 ret.

(* after if23: t'23 = the snapshot state test *)
Definition hcr5_q3_A7 gv L IA NS NSs T m M kes h0 ret FX (a p: val) (b: int) : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._t'21 (Vint b) :: hcr5_q3_Lp gv L kes m h0 ret p a)
  (SEPx (hcr5_q3_R gv L IA NS NSs T m M (@data_at_ HCS Tsh t_mstate (l_st L)) FX))).

(* after the call's two copies: before = the snapshot's chaining key and hash *)
Definition hcr5_q3_A6 gv L IA NS NSs T m M kes h0 ret FX (a p: val) (ck h: list byte) : environ -> mpred :=
  PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret p a)
  (SEPx [@data_at HCS Tsh t_mident (mident_val IA) (l_ia L); itable Tsh (l_ita L) T;
         @data_at W Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L); hnodes_rep4 W (hcr5_head NS) NSs;
         resp_rep Ews m M; wg_consts gv; @data_at_ HCS Tsh t_mstate (l_st L);
         @data_at HCS Tsh t_mstate (mstate_val ck h) (l_before L); FX])).

(* after m_consume_response: mc = the model's result *)
Definition hcr5_q3_A8 gv L IA NS NSs T m M kes h0 ret FX (a p: val) (ck h: list byte)
  (mc: option (list byte * list byte)) : environ -> mpred :=
  PROPx [] (LOCALx (temp HR5._t'20 (Vint (match mc with Some _ => Int.one | None => Int.zero end)) ::
                    hcr5_q3_Lp gv L kes m h0 ret p a)
  (SEPx [@data_at HCS Tsh t_mident (mident_val IA) (l_ia L); itable Tsh (l_ita L) T;
         @data_at W Tsh (tptr t_hnode4) (hcr5_head NS) (l_peers L); hnodes_rep4 W (hcr5_head NS) NSs;
         resp_rep Ews m M; wg_consts gv;
         match mc with
         | Some (ck', h') => @data_at HCS Tsh t_mstate (mstate_val ck' h') (l_st L)
         | None => @data_at_ HCS Tsh t_mstate (l_st L) end;
         @data_at HCS Tsh t_mstate (mstate_val ck h) (l_before L); FX])).

(* CALL = bytes_copy(before.ck, ..); bytes_copy(before.h, ..); MC; MC = t'22 = m_consume_response(..); if (t'22) target = p *)
Definition hcr5_q3_bc1 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_CALL] in
  (match hcr5_q3_CALL with Ssequence s _ => s | _ => Sskip end) in exact x).
Definition hcr5_q3_bc2 : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_CALL] in
  (match hcr5_q3_CALL with Ssequence _ (Ssequence s _) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_mcall : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_CALL] in
  (match hcr5_q3_CALL with Ssequence _ (Ssequence _ (Ssequence s _)) => s | _ => Sskip end) in exact x).
Definition hcr5_q3_mif : statement := ltac:(let x := eval cbv beta iota delta [hcr5_q3_CALL] in
  (match hcr5_q3_CALL with Ssequence _ (Ssequence _ (Ssequence _ s)) => s | _ => Sskip end) in exact x).
Lemma hcr5_q3_call_eq : hcr5_q3_CALL =
  Ssequence hcr5_q3_bc1 (Ssequence hcr5_q3_bc2 (Ssequence hcr5_q3_mcall hcr5_q3_mif)).
Proof. reflexivity. Qed.

(* core: if (p != NULL) { t'87 = p->snap.state; t'23 = t'87 == 1; } else t'23 = 0; *)
Lemma hcr5_q3_k23v {Espec: OracleKind} gv L kes m h0 ret x a pp sn r (rs: @reptype CKS t_prsnap) nx F Rr :
  isptr x ->
  semax D3 (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; @data_at W Ews t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x])))
    hcr5_q3_if23
    (overridePost (PROPx [] (LOCALx (temp HR5._t'21 (Vint (if Int.eq (hs_state (sn_hs sn)) HS_CREATED_INITIATION
                                                          then Int.one else Int.zero)) ::
                                     hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; @data_at W Ews t_hnode4 (pp, (hsnap_val sn, (r, (rs, nx)))) x]))) Rr).
Proof.
  intros Hx. destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_if23. cbn [app]. simplify_func_tycontext.
  forward_if.
  { forward. forward. entailer!.
    all: unfold HS_CREATED_INITIATION; destruct (Int.eq (hs_state (sn_hs sn)) (Int.repr 1)); reflexivity. }
  { exfalso. first [ match goal with Hc: x = nullval |- _ => rewrite Hc in Hx; exact Hx end | exact Hx ]. }
Qed.

(* the node atom with a known snapshot (hn_snap is typed in HNS, hsnap_val in HCS: rewriting one into the
   other inside a Floyd proof costs a 3 s kernel conversion per occurrence; here it is done once) *)
Lemma hcr5_q3_nodeA_eq N nx sn : hn_snap N = hsnap_val sn ->
  hcr5_q3_nodeA N nx = @data_at W Ews t_hnode4 (hn_p N, (hsnap_val sn, (hn_refs N, (hn_rest N, nx)))) (hn_addr N).
Proof. intros Hs. unfold hcr5_q3_nodeA. rewrite Hs. reflexivity. Qed.

Lemma hcr5_q3_k23 {Espec: OracleKind} gv L kes m h0 ret a N nx sn F Rr :
  isptr (hn_addr N) -> hn_snap N = hsnap_val sn ->
  semax D3 (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret (hn_addr N) a) (SEPx [F; hcr5_q3_nodeA N nx])))
    hcr5_q3_if23
    (overridePost (PROPx [] (LOCALx (temp HR5._t'21 (Vint (if Int.eq (hs_state (sn_hs sn)) HS_CREATED_INITIATION
                                                          then Int.one else Int.zero)) ::
                                     hcr5_q3_Lp gv L kes m h0 ret (hn_addr N) a)
              (SEPx [F; hcr5_q3_nodeA N nx]))) Rr).
Proof.
  intros Hx Hs. rewrite (hcr5_q3_nodeA_eq N nx sn Hs). apply hcr5_q3_k23v. exact Hx.
Qed.

(* core: bytes_copy(before.ck, p->snap.chaining_key, 32) *)
Lemma hcr5_q3_cBC1 {Espec: OracleKind} gv L kes m h0 ret x a (ck: list byte) (F: mpred) Rr :
  Zlength ck = 32 -> isptr x ->
  semax D3 (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; hout Tsh 32 (l_before L); hbytes Ews ck (offset_val 248 x)])))
    hcr5_q3_bc1
    (overridePost (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; hbytes Tsh ck (l_before L); hbytes Ews ck (offset_val 248 x)]))) Rr).
Proof.
  intros Hl Hx.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_bc1. cbn [app].
  simplify_func_tycontext.
  forward_call (Tsh, l_before L, Ews, offset_val 248 x, ck).
  2: { rewrite Hl. cancel. }
  { entailer!. rewrite Hl. simpl. rewrite offset_offset_val, isptr_offset_val_zero by auto. reflexivity. }
  entailer!.
Qed.

(* core: bytes_copy(before.h, p->snap.hash, 32) *)
Lemma hcr5_q3_cBC2 {Espec: OracleKind} gv L kes m h0 ret x a (h: list byte) (F: mpred) Rr :
  Zlength h = 32 -> isptr x ->
  semax D3 (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; hout Tsh 32 (offset_val 32 (l_before L)); hbytes Ews h (offset_val 216 x)])))
    hcr5_q3_bc2
    (overridePost (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
              (SEPx [F; hbytes Tsh h (offset_val 32 (l_before L)); hbytes Ews h (offset_val 216 x)]))) Rr).
Proof.
  intros Hl Hx.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_bc2. cbn [app].
  simplify_func_tycontext.
  forward_call (Tsh, offset_val 32 (l_before L), Ews, offset_val 216 x, h).
  2: { rewrite Hl. cancel. }
  { entailer!. rewrite Hl. simpl. rewrite offset_offset_val. reflexivity. }
  entailer!.
Qed.

(* core: t'22 = m_consume_response(&st, &before, p->snap.ephemeral_private, ia.priv, p->snap.preshared_key,
   msg->unencrypted_ephemeral, msg->encrypted_nothing) *)
Lemma hcr5_q3_cMC {Espec: OracleKind} gv L kes m h0 ret x a CK H EPRIV SPRIV PSK E ENCN (F: mpred) Rr :
  isptr x -> isptr m -> Zlength CK = 32 -> Zlength H = 32 -> Zlength EPRIV = 32 -> Zlength SPRIV = 32 ->
  Zlength PSK = 32 -> Zlength E = 32 -> Zlength ENCN = 16 ->
  semax D3 (PROPx [] (LOCALx (hcr5_q3_Lp gv L kes m h0 ret x a)
     (SEPx [F; @data_at_ HCS Tsh t_mstate (l_st L); @data_at HCS Tsh t_mstate (mstate_val CK H) (l_before L);
            hbytes Ews EPRIV (offset_val 56 x); hbytes Ews SPRIV (l_ia L); hbytes Ews PSK (offset_val 184 x);
            hbytes Ews E (offset_val 12 m); hbytes Ews ENCN (offset_val 44 m);
            WgNoise.proof.blake2s.spec.blake2s_globals gv; @zero_page Noise.CS gv])))
    hcr5_q3_mcall
    (overridePost (PROPx [] (LOCALx
       (temp HR5._t'20 (Vint (match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
                             Some _ => Int.one | None => Int.zero end)) :: hcr5_q3_Lp gv L kes m h0 ret x a)
     (SEPx [F; match m_consume_response_model x25519 aead_dec CK H EPRIV SPRIV PSK E ENCN with
               | Some (ck, h) => @data_at HCS Tsh t_mstate (mstate_val ck h) (l_st L)
               | None => @data_at_ HCS Tsh t_mstate (l_st L) end;
            @data_at HCS Tsh t_mstate (mstate_val CK H) (l_before L);
            hbytes Ews EPRIV (offset_val 56 x); hbytes Ews SPRIV (l_ia L); hbytes Ews PSK (offset_val 184 x);
            hbytes Ews E (offset_val 12 m); hbytes Ews ENCN (offset_val 44 m);
            WgNoise.proof.blake2s.spec.blake2s_globals gv; @zero_page Noise.CS gv]))) Rr).
Proof.
  intros Hx Hm HlCK HlH HlE HlS HlP HlEm HlN.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_mcall. cbn [app].
  simplify_func_tycontext.
  forward_call (gv, Tsh, l_st L, Tsh, l_before L, CK, H, Ews, offset_val 56 x, EPRIV, l_ia L, SPRIV,
                offset_val 184 x, PSK, offset_val 12 m, E, offset_val 44 m, ENCN).
  entailer!.
Qed.

(* wrapper: if23 on the node of the entry's peer *)
Lemma hcr5_q3_L23 {Espec: OracleKind} gv L IA NS NSs T m M kes h0 ret FX a E NSa N0 NSb P Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hcr5_head NSs = hcr5_head NS ->
  semax D3 (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0)) hcr5_q3_if23
    (overridePost (hcr5_q3_A7 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0)
       (if Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION then Int.one else Int.zero)) Rr).
Proof.
  intros HNS0 HpA0 HsnN0 HsH.
  unfold hcr5_q3_A4, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hcr5_q3_open NSs NSa N0 NSb HNS0). Intros.
  hcr5_q3_keep [hcr5_q3_nodeA N0 (hcr5_head NSb)] FZ.
  eapply semax_pre; [| eapply hcr5_q3_post; [| apply (hcr5_q3_k23 gv L kes m h0 ret a N0 (hcr5_head NSb)
      (hs_snap_cur T (e_peer E) P) (FRZL FZ)); assumption]].
  - unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!.
  - unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. thaw FZ.
    sep_apply (hcr5_q3_wand1 (hcr5_q3_nodeA N0 (hcr5_head NSb)) (hnodes_rep4 W (hcr5_head NSs) NSs)).
    rewrite HsH. cbn [hs_snap_cur snap_of sn_hs].
    unfold hcr5_q3_A7, hcr5_q3_R, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!.
Qed.

(* if (t'23): the state is not CREATED_INITIATION *)
Lemma hcr5_q3_L23n {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX a E p shp P Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
  Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = false ->
  semax D3 (hcr5_q3_A7 gv L IA NS NSs T m M kes h0 ret FX a p Int.zero)
    (Sifthenelse hcr5_q3_c23 hcr5_q3_CALL Sskip)
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros Hok Hfind Hty HsfP Hst.
  assert (Htg: hcr5_tgt x25519 aead_dec IA T PS M = None).
  { unfold hcr5_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst. reflexivity. }
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  unfold hcr5_q3_A7, hcr5_q3_R, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_c23. cbn [app].
  simplify_func_tycontext.
  forward_if.
  { exfalso. match goal with Hc: _ <> _ |- _ => apply Hc; reflexivity end. }
  forward.
  unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite Htg. cbn [hcr5_tnode hcr5_st_rep app].
  entailer!.
Qed.

(* if (t'23): the state is CREATED_INITIATION: CALL *)
Lemma hcr5_q3_L23c {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX a p Rr :
  semax D3 (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a p) hcr5_q3_CALL
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr) ->
  semax D3 (hcr5_q3_A7 gv L IA NS NSs T m M kes h0 ret FX a p Int.one)
    (Sifthenelse hcr5_q3_c23 hcr5_q3_CALL Sskip)
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros HCALL.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost] in HCALL |- *.
  unfold hcr5_q3_A7, hcr5_q3_Lp, hcr5_Delta, hcr5_q3_c23. unfold hcr5_Delta in HCALL.
  simplify_func_tycontext.
  forward_if.
  { eapply semax_pre; [| exact HCALL].
    unfold hcr5_q3_A4, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!. }
  { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
Qed.

(* wrapper: the two copies into before, then the rest of CALL *)
Lemma hcr5_q3_LBC {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX a E NSa N0 NSb P rest Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) -> hs_ok (p_hs P) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hcr5_head NSs = hcr5_head NS ->
  semax D3 (hcr5_q3_A6 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
    rest (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr) ->
  semax D3 (hcr5_q3_A4 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0))
    (Ssequence hcr5_q3_bc1 (Ssequence hcr5_q3_bc2 rest))
    (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros HNS0 HpA0 HhsP HsnN0 HsH Hrest.
  destruct hcr5_q3_sep_ok as (_ & _ & _ & _ & _ & _ & Sms1 & Sms2 & _).
  pose proof HhsP as (HlE & _ & _ & _ & HlPsk & HlH & HlCk & _).
  unfold hcr5_q3_A4, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hcr5_q3_open NSs NSa N0 NSb HNS0). Intros.
  sep_apply (hcr5_q3_fields T N0 (hcr5_head NSb) (e_peer E) P HsnN0 HhsP).
  sep_apply (Sms1 Tsh (l_before L)). Intros.
  hcr5_q3_keep [hout Tsh 32 (l_before L); hbytes Ews (hs_ck (p_hs P)) (offset_val 248 (hn_addr N0))] FZ.
  eapply semax_seq.
  { eapply semax_pre; [| apply (hcr5_q3_cBC1 gv L kes m h0 ret (hn_addr N0) a (hs_ck (p_hs P)) (FRZL FZ)); assumption].
    unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!. }
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. thaw FZ.
  hcr5_q3_keep [hout Tsh 32 (offset_val 32 (l_before L)); hbytes Ews (hs_hash (p_hs P)) (offset_val 216 (hn_addr N0))] FZ2.
  eapply semax_seq.
  { eapply semax_pre; [| apply (hcr5_q3_cBC2 gv L kes m h0 ret (hn_addr N0) a (hs_hash (p_hs P)) (FRZL FZ2)); assumption].
    unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!. }
  unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. thaw FZ2.
  sep_apply (Sms2 Tsh (hs_ck (p_hs P)) (hs_hash (p_hs P)) (l_before L) ltac:(assumption) HlCk HlH).
  sep_apply (hcr5_q3_unfields N0 (hcr5_head NSb) (p_hs P)).
  sep_apply (hcr5_q3_wand1 (hcr5_q3_nodeA N0 (hcr5_head NSb)) (hnodes_rep4 W (hcr5_head NSs) NSs)).
  rewrite HsH.
  eapply semax_pre; [| exact Hrest].
  unfold hcr5_q3_A6, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!.
Qed.

(* wrapper: the call *)
Lemma hcr5_q3_LMC1 {Espec: OracleKind} gv L IA NS NSs T m M kes h0 ret FX a E NSa N0 NSb P Rr :
  NSs = NSa ++ N0 :: NSb -> isptr (hn_addr N0) ->
  hn_snap N0 = hsnap_val (hs_snap_cur T (e_peer E) P) ->
  hcr5_head NSs = hcr5_head NS -> hs_ok (p_hs P) -> Zlength (mi_priv IA) = 32 ->
  semax D3 (hcr5_q3_A6 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P)))
    hcr5_q3_mcall
    (overridePost (hcr5_q3_A8 gv L IA NS NSs T m M kes h0 ret FX a (hn_addr N0) (hs_ck (p_hs P)) (hs_hash (p_hs P))
       (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
          (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M))) Rr).
Proof.
  intros HNS0 HpA0 HsnN0 HsH HhsP HlIA.
  destruct hcr5_q3_sep_ok as (_ & _ & _ & _ & _ & Spriv & _).
  pose proof HhsP as (HlE & _ & _ & _ & HlPsk & HlH & HlCk & _).
  unfold hcr5_q3_A6, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app].
  rewrite <- HsH. sep_apply (hcr5_q3_open NSs NSa N0 NSb HNS0). Intros.
  sep_apply (hcr5_q3_fields T N0 (hcr5_head NSb) (e_peer E) P HsnN0 HhsP).
  sep_apply (Spriv Tsh IA (l_ia L) HlIA).
  sep_apply (hcr5_q3_split_T (mi_priv IA) (l_ia L)).
  assert_PROP (isptr m) as Hpm.
  { unfold resp_rep. Intros. entailer!.
    all: match goal with Hf: @field_compatible _ _ _ ?mm |- isptr ?mm => exact (field_compatible_isptr _ _ _ Hf) end. }
  sep_apply (hcr5_q3_resp_open M m). Intros.
  match goal with HM: rm_ok M |- _ => rename HM into HrM end.
  pose proof HrM as (HlEm & HlNm & _ & _).
  unfold wg_consts. Intros.
  hcr5_q3_keep [@data_at_ HCS Tsh t_mstate (l_st L);
    @data_at HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L);
    hbytes Ews (hs_eph (p_hs P)) (offset_val 56 (hn_addr N0)); hbytes Ews (mi_priv IA) (l_ia L);
    hbytes Ews (hs_psk (p_hs P)) (offset_val 184 (hn_addr N0)); hbytes Ews (rm_eph M) (offset_val 12 m);
    hbytes Ews (rm_encn M) (offset_val 44 m); WgNoise.proof.blake2s.spec.blake2s_globals gv;
    @zero_page Noise.CS gv] FZ.
  eapply semax_pre; [| eapply hcr5_q3_post; [| apply (hcr5_q3_cMC gv L kes m h0 ret (hn_addr N0) a
      (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P)) (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)
      (FRZL FZ)); assumption]].
  - unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. entailer!.
  - unfold hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars; cbn [app]. thaw FZ.
    sep_apply (hcr5_q3_resp_close M m HrM).
    sep_apply (hcr5_q3_join_T (mi_priv IA) (l_ia L)).
    sep_apply (hcr5_q3_wand1 (hbytes Tsh (mi_priv IA) (l_ia L)) (@data_at HCS Tsh t_mident (mident_val IA) (l_ia L))).
    sep_apply (hcr5_q3_unfields N0 (hcr5_head NSb) (p_hs P)).
    sep_apply (hcr5_q3_wand1 (hcr5_q3_nodeA N0 (hcr5_head NSb)) (hnodes_rep4 W (hcr5_head NSs) NSs)).
    rewrite HsH.
    unfold hcr5_q3_A8, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, wg_consts; cbn [app].
    entailer!.
Qed.

(* if (t'22) target = p; *)
Lemma hcr5_q3_LMC2 {Espec: OracleKind} gv L IA NS NSs PS T m M kes h0 ret FX a E x shp P Rr :
  mi_ok IA = true -> t_find_index T (t_L T) (rm_receiver M) = Some (a, E) ->
  Int.eq (e_type E) IDX_HANDSHAKE = true -> sfind PS (e_peer E) = Some (shp, P) ->
  Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION = true ->
  x = hcr5_nfind NS (e_peer E) ->
  semax D3 (hcr5_q3_A8 gv L IA NS NSs T m M kes h0 ret FX a x (hs_ck (p_hs P)) (hs_hash (p_hs P))
       (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
          (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)))
    hcr5_q3_mif (overridePost (hcr5_q3_OUT gv L IA NS NSs PS T m M kes h0 ret FX) Rr).
Proof.
  intros Hok Hfind Hty HsfP Hst Hx.
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost].
  destruct (m_consume_response_model x25519 aead_dec (hs_ck (p_hs P)) (hs_hash (p_hs P)) (hs_eph (p_hs P))
              (mi_priv IA) (hs_psk (p_hs P)) (rm_eph M) (rm_encn M)) as [[ck h] |] eqn:Hmc.
  - assert (Htg: hcr5_tgt x25519 aead_dec IA T PS M = Some (e_peer E, P, ck, h)).
    { unfold hcr5_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst, Hmc. reflexivity. }
    unfold hcr5_q3_A8, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_mif. cbn [app].
    simplify_func_tycontext.
    forward_if.
    2: { exfalso. match goal with Hc: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward.
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L)).
    unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite Htg.
    cbn [hcr5_tnode hcr5_st_rep app]. rewrite <- Hx.
    entailer!.
  - assert (Htg: hcr5_tgt x25519 aead_dec IA T PS M = None).
    { unfold hcr5_tgt. rewrite Hok, Hfind, Hty, HsfP, Hst, Hmc. reflexivity. }
    unfold hcr5_q3_A8, hcr5_q3_Lp, hcr5_q3_Q, hcr5_lvars, hcr5_Delta, hcr5_q3_mif. cbn [app].
    simplify_func_tycontext.
    forward_if.
    { exfalso. match goal with Hc: _ <> _ |- _ => apply Hc; reflexivity end. }
    forward.
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_before L)).
    unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite Htg.
    cbn [hcr5_tnode hcr5_st_rep app].
    entailer!.
Qed.

Lemma hcr5_q3_sepx {A: Type} (x1 x2 x3 x4 x5 x6 x7 x8: mpred) (B: list mpred) :
  @SEPx A [x1; x2; x3; x4; x5; x6; x7; x8; fold_right_sepcon B] = SEPx (x1 :: x2 :: x3 :: x4 :: x5 :: x6 :: x7 :: x8 :: B).
Proof. unfold SEPx. extensionality rho. simpl. rewrite sepcon_emp. reflexivity. Qed.

(* ---- the start: target = NULL; t'86 = ia.ok; if (t'86) THEN; the frame of SQ2 the block does not read ---- *)
Definition hcr5_q3_FXl gv L FR R S (NS: list hnode4) PS head T KE m M : list mpred :=
  [device_rep Tsh (l_wa L) (hcr5_DAL x25519 R L); ptable Tsh (l_pta L) head;
   @data_at HCS Tsh t_mident (mident_val (hcr5_IB x25519 R)) (l_ib L);
   hbytes Tsh (r5_rawa R) (l_rawa L); hbytes Tsh (r5_rawb R) (l_rawb L);
   peers_rep (peers_after PS (hcr5_res x25519 aead_dec R L T PS M));
   hbytes Tsh (resp_bytes M) (l_img L); kents_rep W (hcr5_khead KE) (map (kent_snapped T) KE);
   hcr5_tok t_resp m; mem_mgr gv; shim_state4 gv S hcr5_w0; noise_globals gv Int64.zero; hcr5_consts gv; FR;
   @data_at CKS Tsh t_devsnap (devsnap_val (hcr5_DAL x25519 R L) head) (l_ds L);
   @data_at CKS Tsh t_shimsnap (shimsnap_val S hcr5_w0) (l_ss L);
   hout Tsh 32 (l_pub L); hout Tsh 92 (l_imga L); @data_at_ HCS Tsh t_mresp (l_mr L);
   @data_at_ HCS Tsh t_mstate (l_cur L); hout Tsh 32 (l_eraw L); hout Tsh 32 (l_ei L)].

Lemma hcr5_q3_L0 {Espec: OracleKind} gv L FR Rr :
  (forall R S NS PS head nb T KE m M,
     hcr5_run_ok R -> hcr5_list_ok L (hcr5_ka KE) NS PS head nb -> hcr5_pool (hcr5_ka KE) PS T -> m <> nullval -> rm_ok M ->
     mi_ok (hcr5_IA x25519 R) = true -> itable_wf T -> Forall isptr (saddrs (t_D T)) ->
     Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x))
       (peers_after PS (hcr5_res x25519 aead_dec R L T PS M)) ->
     Forall isptr (map hn_addr (hnodes_snapped4 T NS PS)) ->
     semax D3 (hcr5_q3_A0 gv L (hcr5_IA x25519 R) NS (hnodes_snapped4 T NS PS) T m M (hcr5_khead KE) (hd nullval (t_L T))
                 (peer_result (hcr5_res x25519 aead_dec R L T PS M))
                 (fold_right_sepcon (hcr5_q3_FXl gv L FR R S NS PS head T KE m M)))
       hcr5_q3_THEN
       (overridePost (hcr5_q3_OUT gv L (hcr5_IA x25519 R) NS (hnodes_snapped4 T NS PS) PS T m M (hcr5_khead KE) (hd nullval (t_L T))
                 (peer_result (hcr5_res x25519 aead_dec R L T PS M))
                 (fold_right_sepcon (hcr5_q3_FXl gv L FR R S NS PS head T KE m M))) Rr)) ->
  semax D3 (hcr5_SQ2 x25519 aead_dec gv L FR) hcr5_Q3 (overridePost (hcr5_SQ3 x25519 aead_dec gv L FR) Rr).
Proof.
  intros HT. rewrite hcr5_q3_eq.
  destruct hcr5_q3_sep_ok as (_ & _ & _ & Sptrs & _ & _ & _ & _ & Sfc).
  destruct Rr as [Rn Rb Rc Rret]. cbn [overridePost] in HT |- *.
  unfold hcr5_SQ2, hcr5_Delta, hcr5_q3_s0, hcr5_q3_s86, hcr5_q3_c86. unfold hcr5_Delta in HT.
  simplify_func_tycontext.
  Intros R S NS PS head nb T KE m M.
  unfold hcr5_lvars, hcr5_scr, hcr5_world, hcr5_globs, hcr5_snaps; cbn [app].
  forward.
  rewrite (hcr5_q3_mident_cs Tsh (hcr5_IA x25519 R)). forward. rewrite <- hcr5_q3_mident_cs.
  destruct (mi_ok (hcr5_IA x25519 R)) eqn:Hok.
  2: {
    forward_if. 1: { exfalso. auto. }
    forward.
    assert (Htg: hcr5_tgt x25519 aead_dec (hcr5_IA x25519 R) T PS M = None).
    { unfold hcr5_tgt. rewrite Hok. reflexivity. }
    unfold hcr5_SQ3. Exists R S NS PS head nb T KE m M.
    unfold hcr5_world, hcr5_globs, hcr5_snaps, hcr5_lvars, hcr5_tg. rewrite Htg.
    cbn [hcr5_tnode hcr5_st_rep app]. entailer!. }
  assert_PROP (itable_wf T) as Hwf. { unfold itable. entailer!. }
  assert_PROP (Forall isptr (saddrs (t_D T))) as Hptr.
  { unfold itable. Intros. sep_apply (hcr5_q3_ptrs (t_L T) (t_D T)). entailer!. }
  assert_PROP (Forall (fun x => @field_compatible W t_peer [] (peer_addr4 x))
       (peers_after PS (hcr5_res x25519 aead_dec R L T PS M))) as Hfc0.
  { sep_apply (Sfc (peers_after PS (hcr5_res x25519 aead_dec R L T PS M))). entailer!. }
  assert_PROP (Forall isptr (map hn_addr (hnodes_snapped4 T NS PS))) as HptrN.
  { sep_apply (Sptrs (hcr5_head NS) (hnodes_snapped4 T NS PS)). entailer!. }
  forward_if; [| exfalso; discriminate].
  eapply semax_pre; [| eapply semax_post; [| | | | apply (HT R S NS PS head nb T KE m M); assumption]].
  - unfold hcr5_q3_A0, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite hcr5_q3_sepx. unfold hcr5_q3_FXl. cbn [app].
    entailer!.
  - cbn [RA_normal]. unfold hcr5_q3_OUT, hcr5_q3_R, hcr5_q3_Q, hcr5_lvars. rewrite hcr5_q3_sepx.
    unfold hcr5_q3_FXl, hcr5_SQ3, hcr5_tg. cbn [app].
    Exists R S NS PS head nb T KE m M. unfold hcr5_world, hcr5_globs, hcr5_snaps, hcr5_lvars, hcr5_tg. cbn [app].
    entailer!.
  - intros. simpl RA_break. apply andp_left2, derives_refl.
  - intros. simpl RA_continue. apply andp_left2, derives_refl.
  - intros. simpl RA_return. apply andp_left2, derives_refl.
Qed.

Lemma hcr5_q3_all {Espec: OracleKind} gv L FR Rr :
  semax D3 (hcr5_SQ2 x25519 aead_dec gv L FR) hcr5_Q3 (overridePost (hcr5_SQ3 x25519 aead_dec gv L FR) Rr).
Proof.
  apply hcr5_q3_L0.
  intros R S NS PS head nb T KE m M Hrun Hlist Hpool Hm HrM Hok Hwf Hptr Hfc0 HptrN.
  destruct hcr5_q3_pure_ok as (Pfind & Phs & Ppool & Plm & Pnode & Psnap & Psupd).
  pose proof Hwf as (HwL & HwI & HwD & HwS).
  rewrite hcr5_q3_then_eq.
  eapply semax_seq; [apply hcr5_q3_Lwalk |].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a E] |] eqn:Hfind.
  2: { apply hcr5_q3_Lnf; assumption. }
  destruct (Int.eq (e_type E) IDX_HANDSHAKE) eqn:Hty.
  2: { eapply hcr5_q3_Lnhs; eassumption. }
  apply (hcr5_q3_Lhs _ _ _ _ _ _ _ _ _ _ _ _ _ _ a E Hfind Hty).
  destruct (Pfind T (t_L T) (rm_receiver M) a E Hfind) as [Ha HtE].
  assert (HtyE: e_type E = IDX_HANDSHAKE) by (apply Int.same_if_eq; exact Hty).
  destruct (Phs (hcr5_ka KE) PS T a E Hpool HwD HtE HtyE) as (Hae & shp & P & HsfP & HinP).
  assert (Hpeq: map peer_addr4 (peers_after PS (hcr5_res x25519 aead_dec R L T PS M)) = map peer_addr4 PS).
  { unfold peers_after. destruct (hcr5_res x25519 aead_dec R L T PS M) as [[? ?] |];
      [apply Psupd | reflexivity]. }
  assert (Hhp: hnodes_peers4 NS PS) by (destruct Hlist as (? & ? & ? & ? & ?); assumption).
  assert (HndP: NoDup (map peer_addr4 PS)) by (destruct Hlist as (? & ? & ? & ? & ? & ?); assumption).
  destruct (Psnap T NS PS Hhp) as (HsA & HsP & HsH).
  assert (HfcP: forall q, In q (map hn_p (hnodes_snapped4 T NS PS)) ->
            @field_compatible W t_peer [] q /\ In (hs_addr q) (saddrs (t_D T))).
  { intros q Hq. rewrite HsP in Hq. unfold hnodes_peers4 in Hhp. rewrite Hhp in Hq. split.
    - rewrite <- Hpeq in Hq. rewrite in_map_iff in Hq. destruct Hq as (x & <- & Hx).
      rewrite Forall_forall in Hfc0. apply (Hfc0 x Hx).
    - rewrite in_map_iff in Hq. destruct Hq as ([[q' shq] Q] & Hq' & Hx). simpl in Hq'. subst q'.
      eapply Ppool; eauto. }
  assert (HaD: In a (saddrs (t_D T))) by (apply HwI; exact Ha).
  assert (Hpa: isptr (hs_addr (e_peer E))).
  { rewrite <- Hae. rewrite Forall_forall in Hptr. apply Hptr. exact HaD. }
  rewrite hcr5_q3_hs_eq.
  eapply semax_seq; [apply hcr5_q3_Lsp |].
  eapply semax_seq; [apply hcr5_q3_Lnode; assumption |].
  assert (Hlm: hcr5_q3_lm (hnodes_snapped4 T NS PS) a = hcr5_nfind NS (e_peer E))
    by (rewrite Hae; apply Plm; auto).
  destruct (Pnode T NS PS (e_peer E) shp P Hhp HsfP)
    as (NSa & N0 & NSb & HNS0 & HaN0 & HpN0 & HsnN0 & _).
  assert (HpA0: isptr (hn_addr N0)).
  { rewrite Forall_forall in HptrN. apply HptrN. rewrite HNS0, map_app. apply in_or_app. right. left. reflexivity. }
  assert (HhsP: hs_ok (p_hs P)).
  { destruct Hlist as (Hpok & _). rewrite Forall_forall in Hpok. apply (Hpok _ HinP). }
  assert (HlIA: Zlength (mi_priv (hcr5_IA x25519 R)) = 32).
  { unfold hcr5_IA, mident_of. cbn [mi_priv]. apply hcr5_q3_clamp_len. destruct Hrun as (? & _). assumption. }
  assert (Hp0: hcr5_q3_lm (hnodes_snapped4 T NS PS) a = hn_addr N0) by (rewrite Hlm, HaN0; reflexivity).
  rewrite Hp0.
  eapply semax_seq; [eapply hcr5_q3_L23; eassumption |].
  destruct (Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION) eqn:Hst.
  2: { eapply hcr5_q3_L23n; eassumption. }
  apply hcr5_q3_L23c.
  rewrite hcr5_q3_call_eq.
  eapply hcr5_q3_LBC; try eassumption.
  eapply semax_seq; [eapply hcr5_q3_LMC1; eassumption |].
  eapply hcr5_q3_LMC2; eassumption.
Qed.

End Q3.
