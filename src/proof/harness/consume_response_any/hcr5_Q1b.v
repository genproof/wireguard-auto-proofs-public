(* law consume_response_any, phase Q1b: statement 3 of P6's then-branch: the mode-1/2 block (B's response built by the model from nb's peer; mode 2: one byte changed).
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
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers: compspecs conversions, the node / peer / pool entry of nb      *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcr5_q1b_cce_N : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.
#[local] Instance hcr5_q1b_cce_H : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.
#[local] Instance hcr5_q1b_cce_K : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

Lemma hcr5_q1b_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

Lemma hcr5_q1b_hb_W sh bs p :
  hbytes sh bs p = @data_at W_consume_response_any sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof. unfold hbytes. apply (@hcr5_q1b_cs_eq HCS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1b_hb_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hcr5_q1b_resp_W sh M p :
  @data_at Noise.CS sh t_resp (resp_val M) p = @data_at W_consume_response_any sh t_resp (resp_val M) p.
Proof. apply (@hcr5_q1b_cs_eq Noise.CS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1b_node_W v l :
  @data_at CKS Ews t_hnode4 v l = @data_at W_consume_response_any Ews t_hnode4 v l.
Proof. apply (@hcr5_q1b_cs_eq CKS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1b_entry_W sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p =
  @data_at W_consume_response_any sh t_entry_s (entry_val E n h) p.
Proof. apply (@hcr5_q1b_cs_eq Noise.CS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

(* Tsh = Ews + its complement *)
Lemma hcr5_q1b_hb_split bs p : hbytes Tsh bs p = (hbytes Ews bs p * hbytes (Share.comp Ews) bs p)%logic.
Proof. unfold hbytes. symmetry. apply data_at_share_join, join_comp_Tsh. Qed.

(* the node nb of the list, with a wand to put it back *)
Lemma hcr5_q1b_node NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W_consume_response_any l NS |--
  EX N: hnode4, EX nx: val, !! (In N NS /\ hn_addr N = a) &&
    (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) a *
     (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) a -*
      hnodes_rep4 W_consume_response_any l NS)).
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl hnodes_rep4. Intros nx.
  destruct (eq_dec (hn_addr N) a) as [Ha | Ha].
  - subst a l. Exists N nx. entailer!. left; reflexivity. rewrite <- wand_sepcon_adjoint. Exists nx. entailer!.
  - assert (Hin': In a (map hn_addr NS)) by (destruct Hin; [contradiction | auto]).
    sep_apply (IH nx a Hin'). Intros N' nx'. Exists N' nx'. entailer!. right; auto.
    rewrite <- wand_sepcon_adjoint.
    match goal with |- context [(?D -* ?X)] => sep_apply (modus_ponens_wand D X) end.
    Exists nx. entailer!.
Qed.

(* a peer of the list *)
Lemma hcr5_q1b_peer PS a : In a (map peer_addr4 PS) ->
  exists sh P PS', In (a, sh, P) PS /\ peers_rep PS = (peer_rep sh a P * peers_rep PS')%logic.
Proof.
  intros Hin. apply in_map_iff in Hin. destruct Hin as [[[x sh] P] [Hx Hin]]. simpl in Hx. subst x.
  destruct (in_split _ _ Hin) as (PS1 & PS2 & ->).
  exists sh, P, (PS1 ++ PS2). split; [exact Hin |].
  unfold peers_rep. rewrite !iter_sepcon_app. simpl.
  rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ PS1)). reflexivity.
Qed.

(* an entry of the pool *)
Lemma hcr5_q1b_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hcr5_q1b_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at W_consume_response_any sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hcr5_q1b_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite !iter_sepcon_app. simpl. unfold pool_item_rep at 2, entry_at. rewrite hcr5_q1b_entry_W.
    rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

Lemma hcr5_q1b_pool_in PS D : Forall2 hcr5_hs_ok PS D ->
  forall a sh P, In (a, sh, P) PS -> In (hs_addr a) (saddrs D).
Proof.
  induction 1 as [| y x PS D Hyx _ IH]; intros a sh P Hin; [contradiction |].
  destruct Hin as [-> | Hin].
  - destruct x as [[b shb] E]. destruct Hyx as [-> _]. left; reflexivity.
  - right. eapply IH; eauto.
Qed.

Lemma hcr5_q1b_skipn_in {A: Type} n (D: list (val * share * A)) a :
  In a (saddrs (skipn n D)) -> In a (saddrs D).
Proof.
  unfold saddrs. intros H. rewrite <- (firstn_skipn n D), map_app. apply in_or_app; right; exact H.
Qed.

(* the entry as a field of the handshake *)
Lemma hcr5_q1b_entry_fld sh (v: @reptype W_consume_response_any t_entry_s) h :
  @field_compatible W_consume_response_any t_hs [] h ->
  @field_at W_consume_response_any sh t_hs (DOT HR5._entry) v h = @data_at W_consume_response_any sh t_entry_s v h.
Proof.
  intros Hf. rewrite field_at_data_at. unfold field_address. rewrite if_true.
  - simpl. rewrite isptr_offset_val_zero by (destruct Hf; auto). reflexivity.
  - apply field_compatible_cons; split; [unfold in_members; simpl; left; reflexivity | exact Hf].
Qed.

(* byte fields of the handshake as hbytes *)
Ltac hcr5_q1b_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_consume_response_any _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite hcr5_q1b_hb_W, Hl; reflexivity.

Lemma hcr5_q1b_hs_ck sh H h : Zlength (hs_ck H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h =
  hbytes sh (hs_ck H) (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) h).
Proof. hcr5_q1b_hsf_tac. Qed.
Lemma hcr5_q1b_hs_hash sh H h : Zlength (hs_hash H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._hash) (bytes (hs_hash H)) h =
  hbytes sh (hs_hash H) (@field_address W_consume_response_any t_hs (DOT HR5._hash) h).
Proof. hcr5_q1b_hsf_tac. Qed.
Lemma hcr5_q1b_hs_eph sh H h : Zlength (hs_eph H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._ephemeral_private) (bytes (hs_eph H)) h =
  hbytes sh (hs_eph H) (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) h).
Proof. hcr5_q1b_hsf_tac. Qed.
Lemma hcr5_q1b_hs_psk sh H h : Zlength (hs_psk H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._preshared_key) (bytes (hs_psk H)) h =
  hbytes sh (hs_psk H) (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) h).
Proof. hcr5_q1b_hsf_tac. Qed.

(* the harness structs and the message, field by field *)
Lemma hcr5_q1b_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W_consume_response_any sh t_mident (mident_val I) p.
Proof. apply (@hcr5_q1b_cs_eq HCS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1b_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (@field_at W_consume_response_any sh t_mident [StructField HR5._priv] (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (@field_address W_consume_response_any t_mident [StructField HR5._pub] p) *
   @field_at W_consume_response_any sh t_mident [StructField HR5._ok] (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.
Proof.
  intros Hl. rewrite hcr5_q1b_mident_W, hcr5_q1b_hb_W, Hl. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident [StructField HR5._pub]). apply pred_ext; cancel.
Qed.

Lemma hcr5_q1b_mstate_split sh p :
  @data_at_ HCS sh t_mstate p =
  (hout sh 32 (@field_address W_consume_response_any t_mstate [StructField HR5._ck] p) *
   hout sh 32 (@field_address W_consume_response_any t_mstate [StructField HR5._h] p))%logic.
Proof.
  rewrite hcr5_conv_mstate, !hcr5_conv_bytes. rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HR5._ck]), (field_at_data_at sh t_mstate [StructField HR5._h]).
  rewrite <- !data_at__eq. reflexivity.
Qed.

Lemma hcr5_q1b_mstate_join sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  (hbytes sh ck (@field_address W_consume_response_any t_mstate [StructField HR5._ck] p) *
   hbytes sh h (@field_address W_consume_response_any t_mstate [StructField HR5._h] p))%logic =
  @data_at HCS sh t_mstate (mstate_val ck h) p.
Proof.
  intros H1 H2. rewrite !hcr5_q1b_hb_W, H1, H2.
  rewrite (@hcr5_q1b_cs_eq HCS W_consume_response_any _ sh t_mstate (mstate_val ck h) (mstate_val ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HR5._ck]), (field_at_data_at sh t_mstate [StructField HR5._h]).
  reflexivity.
Qed.

Lemma hcr5_q1b_mresp_W sh E encn ep ck h p :
  @data_at HCS sh t_mresp (mresp_val E encn ep ck h) p =
  @data_at W_consume_response_any sh t_mresp (mresp_val E encn ep ck h) p.
Proof. apply (@hcr5_q1b_cs_eq HCS W_consume_response_any _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hcr5_q1b_mresp_split sh E encn ep ck h p :
  Zlength E = 32 -> Zlength encn = 16 ->
  @data_at HCS sh t_mresp (mresp_val E encn ep ck h) p =
  (hbytes sh E (@field_address W_consume_response_any t_mresp [StructField HR5._ephemeral] p) *
   hbytes sh encn (@field_address W_consume_response_any t_mresp [StructField HR5._enc_nothing] p) *
   @field_at W_consume_response_any sh t_mresp [StructField HR5._eph_priv] (bytes ep) p *
   @field_at W_consume_response_any sh t_mresp [StructField HR5._st] (bytes ck, bytes h) p)%logic.
Proof.
  intros H1 H2. rewrite hcr5_q1b_mresp_W, !hcr5_q1b_hb_W, H1, H2. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mresp [StructField HR5._ephemeral]).
  rewrite (field_at_data_at sh t_mresp [StructField HR5._enc_nothing]). apply pred_ext; cancel.
Qed.

Lemma hcr5_q1b_mresp_join sh E encn ep ck h p :
  Zlength E = 32 -> Zlength encn = 16 ->
  (hbytes sh E (@field_address W_consume_response_any t_mresp [StructField HR5._ephemeral] p) *
   hbytes sh encn (@field_address W_consume_response_any t_mresp [StructField HR5._enc_nothing] p) *
   @field_at W_consume_response_any sh t_mresp [StructField HR5._eph_priv] (bytes ep) p *
   @field_at W_consume_response_any sh t_mresp [StructField HR5._st] (bytes ck, bytes h) p
   |-- @data_at_ HCS sh t_mresp p)%logic.
Proof.
  intros H1 H2. rewrite <- (hcr5_q1b_mresp_split sh E encn ep ck h p H1 H2). apply data_at_data_at_.
Qed.

Lemma hcr5_q1b_resp_split sh ty se re eph encn mac1 mac2 m :
  Zlength eph = 32 -> Zlength encn = 16 ->
  @data_at Noise.CS sh t_resp (resp_val (mkRM ty se re eph encn mac1 mac2)) m =
  (@field_at W_consume_response_any sh t_resp [StructField HR5._header] (Vint ty) m *
   @field_at W_consume_response_any sh t_resp [StructField HR5._sender_index] (Vint se) m *
   @field_at W_consume_response_any sh t_resp [StructField HR5._receiver_index] (Vint re) m *
   hbytes sh eph (@field_address W_consume_response_any t_resp [StructField HR5._unencrypted_ephemeral] m) *
   hbytes sh encn (@field_address W_consume_response_any t_resp [StructField HR5._encrypted_nothing] m) *
   @field_at W_consume_response_any sh t_resp [StructField HR5._macs] (bytes mac1, bytes mac2) m)%logic.
Proof.
  intros H1 H2. rewrite hcr5_q1b_resp_W, !hcr5_q1b_hb_W, H1, H2. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_resp [StructField HR5._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_resp [StructField HR5._encrypted_nothing]). apply pred_ext; cancel.
Qed.

Lemma hcr5_q1b_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hcr5_q1b_nd (bs: list Z) n p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_consume_response_any Tsh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. rewrite hcr5_q1b_hb_W, Zlength_map, Hl, hcr5_q1b_map_Vint by auto. reflexivity.
Qed.

Lemma hcr5_q1b_Znth_bytes l i : 0 <= i < Zlength l -> Znth i (bytes l) = Vubyte (Znth i l).
Proof. intros Hi. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

(* one byte of a buffer xor'ed (the stored value is cast to unsigned char) *)
Lemma hcr5_q1b_upd_bytes l i x : 0 <= i < Zlength l ->
  upd_Znth i (bytes l) (Vint (Int.zero_ext 8 x)) = bytes (upd_Znth i l (Byte.repr (Int.unsigned x))).
Proof.
  intros Hi. unfold bytes. rewrite <- upd_Znth_map. f_equal. unfold Vubyte. f_equal.
  rewrite Byte.unsigned_repr_eq. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (cbn; lia). reflexivity.
Qed.

Lemma hcr5_q1b_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros Hl. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

(* a node of the list is a valid pointer (the comparison nb != NULL) *)
Lemma hcr5_q1b_node_valid NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W_consume_response_any l NS |-- valid_pointer a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

(* nb's peer, opened at the four byte fields the block reads (the rest kept in one predicate) *)
Definition hcr5_q1b_prest (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS Ews t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS Ews t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep Ews (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS Ews t_hs [StructField I._state] (Vint (hs_state H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._static_identity] (hs_sid H) h *
   @field_at Noise.CS Ews t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   @field_at Noise.CS Ews t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS Ews t_hs [StructField I._lock] lk h) *
   spacer Ews 36 40 h * spacer Ews 300 304 h *
   @field_at Noise.CS Ews t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep Ews (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS Ews t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS Ews t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS Ews t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer Ews 9 16 p * spacer Ews 476 480 p)%logic.

Definition hcr5_q1b_hsb (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (hbytes Ews (hs_ck H) (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) h) *
   hbytes Ews (hs_hash H) (@field_address W_consume_response_any t_hs (DOT HR5._hash) h) *
   hbytes Ews (hs_eph H) (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) h) *
   hbytes Ews (hs_psk H) (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) h))%logic.

Lemma hcr5_q1b_peer_open p P :
  peer_rep Ews p P =
  (!! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P) /\
       @field_compatible W_consume_response_any t_hs [] (hs_addr p)) &&
   (hcr5_q1b_hsb p P * hcr5_q1b_prest p P))%logic.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros.
    assert (Hok := H0). destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hcr5_q1b_hs_ck Ews (p_hs P) (hs_addr p) L7), (hcr5_q1b_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hcr5_q1b_hs_eph Ews (p_hs P) (hs_addr p) L1), (hcr5_q1b_hs_psk Ews (p_hs P) (hs_addr p) L5).
    unfold hcr5_q1b_hsb, hcr5_q1b_prest. Intros lk.
    assert_PROP (@field_compatible Noise.CS t_hs (DOT I._state) (hs_addr p)) as Hf by entailer!.
    apply andp_right.
    + apply prop_right. split; [exact H | split; [exact Hok |]].
      apply field_compatible_cons in Hf. destruct Hf as [_ Hf].
      apply (@field_compatible_change_composite Noise.CS W_consume_response_any _ t_hs) in Hf;
        [exact Hf | reflexivity].
    + Exists lk. cancel.
  - Intros. destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold peer_rep, hs_rep, hcr5_q1b_hsb, hcr5_q1b_prest.
    rewrite (hcr5_q1b_hs_ck Ews (p_hs P) (hs_addr p) L7), (hcr5_q1b_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hcr5_q1b_hs_eph Ews (p_hs P) (hs_addr p) L1), (hcr5_q1b_hs_psk Ews (p_hs P) (hs_addr p) L5).
    Intros lk. Exists lk. entailer!. unfold hs_ok; auto 10.
Qed.

Lemma hcr5_q1b_peer_fold p P :
  @field_compatible Noise.CS t_peer [] p -> hs_ok (p_hs P) -> @field_compatible W_consume_response_any t_hs [] (hs_addr p) ->
  (hcr5_q1b_hsb p P * hcr5_q1b_prest p P |-- peer_rep Ews p P)%logic.
Proof. intros H1 H2 H3. rewrite hcr5_q1b_peer_open. entailer!. Qed.

Lemma hcr5_q1b_peer_fold2 p P :
  @field_compatible Noise.CS t_peer [] p -> hs_ok (p_hs P) -> @field_compatible W_consume_response_any t_hs [] (hs_addr p) ->
  (hbytes Ews (hs_ck (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._chaining_key) (hs_addr p)) *
   hbytes Ews (hs_hash (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._hash) (hs_addr p)) *
   hbytes Ews (hs_eph (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._ephemeral_private) (hs_addr p)) *
   hbytes Ews (hs_psk (p_hs P)) (@field_address W_consume_response_any t_hs (DOT HR5._preshared_key) (hs_addr p)) *
   hcr5_q1b_prest p P |-- peer_rep Ews p P)%logic.
Proof.
  intros H1 H2 H3. eapply derives_trans; [| apply hcr5_q1b_peer_fold; auto]. unfold hcr5_q1b_hsb. cancel.
Qed.

Lemma hcr5_q1b_hb_join bs p : (hbytes Ews bs p * hbytes (Share.comp Ews) bs p |-- hbytes Tsh bs p)%logic.
Proof. rewrite hcr5_q1b_hb_split. apply derives_refl. Qed.

Lemma hcr5_q1b_mstate_joind sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  (hbytes sh ck (@field_address W_consume_response_any t_mstate [StructField HR5._ck] p) *
   hbytes sh h (@field_address W_consume_response_any t_mstate [StructField HR5._h] p) |--
   @data_at HCS sh t_mstate (mstate_val ck h) p)%logic.
Proof. intros H1 H2. rewrite (hcr5_q1b_mstate_join sh ck h p H1 H2). apply derives_refl. Qed.

Lemma hcr5_q1b_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  (@field_at W_consume_response_any sh t_mident [StructField HR5._priv] (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (@field_address W_consume_response_any t_mident [StructField HR5._pub] p) *
   @field_at W_consume_response_any sh t_mident [StructField HR5._ok] (Vint (if mi_ok I then Int.one else Int.zero)) p
   |-- @data_at HCS sh t_mident (mident_val I) p)%logic.
Proof. intros Hl. rewrite (hcr5_q1b_mident_split sh I p Hl). apply derives_refl. Qed.

Lemma hcr5_q1b_resp_join sh ty se re eph encn mac1 mac2 m :
  Zlength eph = 32 -> Zlength encn = 16 -> Zlength mac1 = 16 -> Zlength mac2 = 16 ->
  (@field_at W_consume_response_any sh t_resp [StructField HR5._header] (Vint ty) m *
   @field_at W_consume_response_any sh t_resp [StructField HR5._sender_index] (Vint se) m *
   @field_at W_consume_response_any sh t_resp [StructField HR5._receiver_index] (Vint re) m *
   hbytes sh eph (@field_address W_consume_response_any t_resp [StructField HR5._unencrypted_ephemeral] m) *
   hbytes sh encn (@field_address W_consume_response_any t_resp [StructField HR5._encrypted_nothing] m) *
   @field_at W_consume_response_any sh t_resp [StructField HR5._macs] (bytes mac1, bytes mac2) m
   |-- resp_rep sh m (mkRM ty se re eph encn mac1 mac2))%logic.
Proof.
  intros H1 H2 H3 H4. unfold resp_rep.
  rewrite (hcr5_q1b_resp_split sh ty se re eph encn mac1 mac2 m H1 H2).
  apply andp_right; [apply prop_right; unfold rm_ok; simpl; auto | apply derives_refl].
Qed.

(* the pieces of the statement: the block (then-branch of if (mode != 0 && nb != NULL)) and its mode-2 tail *)
Definition hcr5_q1b_body : statement :=
  ltac:(let x := eval cbv delta [hcr5_Q1b] in hcr5_Q1b in
        match x with Ssequence _ (Sifthenelse _ ?b _) => exact b end).
Definition hcr5_q1b_s2 : statement :=
  ltac:(let x := eval cbv delta [hcr5_q1b_body] in hcr5_q1b_body in
        match x with Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ (Ssequence _ ?s))))) => exact s end).

Local Open Scope logic.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Section Q1b.
Local Open Scope Z_scope.

(* the block's start: mode <> 0, nb <> NULL *)
Definition hcr5_q1b_pre (gv: globals) (L: hcr5_loc) (FR: mpred) (R: hcr5_run) (S: shim) (NS: list hnode4)
  (PS: list (val * share * peer)) (head nb: val) (T: tstate) (KE: list kent4) (m: val) (M: resp_msg)
  (mode: Z) : environ -> mpred :=
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval; rm_ok M;
         0 <= mode < 3; nb <> nullval; mode <> 0]
  (LOCALx ([temp HR5._nb nb; temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._mode (Vint (Int.repr mode))]
           ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

(* before the mode-2 tail: msg holds some well-formed response *)
Definition hcr5_q1b_mid (gv: globals) (L: hcr5_loc) (FR: mpred) (R: hcr5_run) (S: shim) (NS: list hnode4)
  (PS: list (val * share * peer)) (head nb: val) (T: tstate) (KE: list kent4) (m: val)
  (mode: Z) : environ -> mpred :=
  EX M: resp_msg,
  PROPx [hcr5_run_ok R; hcr5_list_ok L (hcr5_ka KE) NS PS head nb; hcr5_pool (hcr5_ka KE) PS T; m <> nullval; rm_ok M;
         0 <= mode < 3]
  (LOCALx ([temp HR5._kes (hcr5_khead KE); temp HR5._msg m; temp HR5._mode (Vint (Int.repr mode))]
           ++ hcr5_lvars gv L)
  (SEPx (hcr5_world x25519 R L NS NS head T ++
         [peers_rep PS; hout Tsh 92 (l_img L); kents_rep W (hcr5_khead KE) KE;
          hcr5_tok t_resp m; resp_rep Ews m M] ++
         hcr5_globs gv S FR ++ hcr5_snaps0 L ++ hcr5_scr L))).

Ltac hcr5_q1b_ur :=
  repeat match goal with Hc: context [Int64.unsigned (Int64.repr ?x)] |- _ =>
    rewrite (Int64.unsigned_repr x) in Hc by rep_lia end.

Lemma hcr5_q1b_s2_ok {Espec: OracleKind} gv L FR R S NS PS head nb T KE m mode Rr :
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcr5_q1b_mid gv L FR R S NS PS head nb T KE m mode) hcr5_q1b_s2
    (overridePost (hcr5_SQ1b x25519 gv L FR) Rr).
Proof.
  destruct Rr as [r1 r2 r3 r4]. unfold overridePost.
  unfold hcr5_q1b_mid, hcr5_Delta, hcr5_q1b_s2. simplify_func_tycontext. abbreviate_semax.
  Intros M.
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
  forward_if.
  { forward_call tt. Intros kk.
    forward.
    forward_call tt. Intros dd.
    forward.
    { entailer!. split; [| intros [_ Hc]; discriminate]. unfold Int.mods.
      rewrite (Int.signed_repr dd) by rep_lia. rewrite (Int.signed_repr 255) by rep_lia.
      pose proof (Z.rem_bound_pos dd 255 ltac:(lia) ltac:(lia)). rewrite Int.signed_repr by rep_lia. rep_lia. }
    assert (Hk: Int64.modu (Int64.repr kk) (Int64.repr (Int.signed (Int.repr 60))) = Int64.repr (kk mod 60)).
    { change (Int.signed (Int.repr 60)) with 60.
      unfold Int64.modu. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
    rewrite Hk.
    assert (Hkr: 0 <= kk mod 60 < 60) by (apply Z.mod_pos_bound; lia).
    set (dv := Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr 1) (Int.mods (Int.repr dd) (Int.repr 255))))).
    unfold resp_rep. Intros. rewrite hcr5_q1b_resp_W.
    destruct M as [ty se re eph encn mac1 mac2].
    match goal with Hm: rm_ok _ |- _ => destruct Hm as (Hl1 & Hl2 & Hl3 & Hl4) end.
    cbn [rm_eph rm_encn rm_mac1 rm_mac2] in *.
    forward_if.
    { forward. forward.
      unfold hcr5_SQ1b. Exists R S NS PS head nb T KE m (mkRM ty se (Int.xor re dv) eph encn mac1 mac2).
      unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
      unfold resp_rep. rewrite hcr5_q1b_resp_W. entailer!. unfold rm_ok; simpl; repeat split; auto. }
    hcr5_q1b_ur.
    forward_if.
    { hcr5_q1b_ur.
      unfold resp_val. cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
      forward.
      { entailer!. try rewrite hcr5_q1b_Znth_bytes by lia. exact (tc_val_Vubyte _). }
      rewrite hcr5_q1b_Znth_bytes by lia.
      forward.
      rewrite hcr5_q1b_upd_bytes by lia.
      unfold hcr5_SQ1b.
      Exists R S NS PS head nb T KE m (mkRM ty se re (upd_Znth (kk mod 60 - 12) eph (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth (kk mod 60 - 12) eph))) dv)))) encn mac1 mac2).
      unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
      unfold resp_rep. rewrite hcr5_q1b_resp_W. unfold resp_val.
      cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
      entailer!. unfold rm_ok; simpl; rewrite ?upd_Znth_Zlength by lia; repeat split; auto. }
    { hcr5_q1b_ur.
      unfold resp_val. cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
      forward.
      { entailer!. try rewrite hcr5_q1b_Znth_bytes by lia. exact (tc_val_Vubyte _). }
      rewrite hcr5_q1b_Znth_bytes by lia.
      forward.
      rewrite hcr5_q1b_upd_bytes by lia.
      unfold hcr5_SQ1b.
      Exists R S NS PS head nb T KE m (mkRM ty se re eph (upd_Znth (kk mod 60 - 44) encn (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth (kk mod 60 - 44) encn))) dv)))) mac1 mac2).
      unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
      unfold resp_rep. rewrite hcr5_q1b_resp_W. unfold resp_val.
      cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
      entailer!. unfold rm_ok; simpl; rewrite ?upd_Znth_Zlength by lia; repeat split; auto. }
  }
  { forward. unfold hcr5_SQ1b. Exists R S NS PS head nb T KE m M.
    unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app]. entailer!. }
Qed.

Lemma hcr5_q1b_cresp_len CK H EI SI PSK ERAW E encn ep ck h :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = Some (E, encn, ep, ck, h) ->
  Zlength E = 32 /\ Zlength encn = 16.
Proof.
  intros Hx Ha Hm. unfold m_create_response_model in Hm.
  repeat match type of Hm with context [if ?c then _ else _] => destruct c end; try discriminate.
  inversion Hm; subst. rewrite (aead_enc_length _ _ Ha). auto.
Qed.

Lemma hcr5_q1b_body_ok {Espec: OracleKind} gv L FR R S NS PS head nb T KE m M mode Rr :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcr5_q1b_pre gv L FR R S NS PS head nb T KE m M mode) hcr5_q1b_body
    (overridePost (hcr5_SQ1b x25519 gv L FR) Rr).
Proof.
  intros HH. destruct Rr as [r1 r2 r3 r4]. unfold overridePost.
  unfold hcr5_q1b_pre, hcr5_Delta, hcr5_q1b_body. simplify_func_tycontext. abbreviate_semax.
  Intros.
  destruct HH as (Hx & Ha & Hxa & Hrep).
  assert (Hlist := H0). destruct H0 as (Hpok & Hwf & Hch & Hnp & Hnd & Hnb).
  destruct Hnb as [Hnb | Hin]; [contradiction |].
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
  sep_apply (hcr5_q1b_node NS (hcr5_head NS) nb Hin). Intros N nx.
  match goal with Hn: In N NS |- _ => rename Hn into HinN end.
  match goal with Hn: hn_addr N = nb |- _ => rename Hn into HaN end. subst nb.
  rewrite hcr5_q1b_node_W.
  assert (Hinp: In (hn_p N) (map peer_addr4 PS)) by (rewrite <- Hnp; apply in_map; exact HinN).
  destruct (hcr5_q1b_peer PS (hn_p N) Hinp) as (sh & P & PS' & HinP & Heq).
  assert (Hsh: sh = Ews).
  { rewrite Forall_forall in Hpok. specialize (Hpok _ HinP). destruct Hpok as [Hs _]. exact Hs. }
  subst sh.
  rewrite Heq, hcr5_q1b_peer_open. Intros.
  match goal with Hc: @field_compatible _ t_peer [] _ |- _ => rename Hc into Hfp end.
  match goal with Hc: hs_ok _ |- _ => rename Hc into Hok end.
  match goal with Hc: field_compatible t_hs [] _ |- _ => rename Hc into Hfh end.
  forward.
  forward.
  match goal with |- context [temp HR5._h ?v] => replace v with (hs_addr (hn_p N)) by (unfold hs_addr; reflexivity) end.
  rewrite <- hcr5_q1b_node_W.
  sep_apply (modus_ponens_wand (@data_at CKS Ews t_hnode4 (hn_p N, (hn_snap N, (hn_refs N, (hn_rest N, nx)))) (hn_addr N)) (hnodes_rep4 W (hcr5_head NS) NS)).
  pose proof Hok as (Le & Lrs & Lre & Lss & Lpsk & Lh & Lck & Lts).
  rewrite (hcr5_conv_bytes Tsh 32 (l_eraw L)).
  forward_call (l_eraw L, 32, Tsh). Intros er.
  rewrite (hcr5_q1b_nd er 32 (l_eraw L)) by tauto.
  assert_PROP (@field_compatible HCS t_mstate [] (l_cur L)) as Hfc. { entailer!. }
  apply (@field_compatible_change_composite HCS W _ t_mstate) in Hfc; [| reflexivity].
  rewrite (hcr5_q1b_mstate_split Tsh (l_cur L)).
  unfold hcr5_q1b_hsb. Intros.
  forward_call (Tsh, field_address t_mstate (DOT HR5._ck) (l_cur L), Ews, field_address t_hs (DOT HR5._chaining_key) (hs_addr (hn_p N)), hs_ck (p_hs P)).
  { entailer!. rewrite Lck. simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
  { rewrite Lck. cancel. }
  forward_call (Tsh, field_address t_mstate (DOT HR5._h) (l_cur L), Ews, field_address t_hs (DOT HR5._hash) (hs_addr (hn_p N)), hs_hash (p_hs P)).
  { entailer!. rewrite Lh. simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
  { rewrite Lh. cancel. }
  change (hcr5_consts gv) with (hbytes Ers basepoint9 (gv HR5._x_consume_response_any__M_BASEPOINT)).
  forward_call (Tsh, l_ei L, Ews, field_address t_hs (DOT HR5._ephemeral_private) (hs_addr (hn_p N)), hs_eph (p_hs P),
                Ers, gv HR5._x_consume_response_any__M_BASEPOINT, basepoint9).
  change (hbytes Ers basepoint9 (gv HR5._x_consume_response_any__M_BASEPOINT)) with (hc_const gv HR5._x_consume_response_any__M_BASEPOINT basepoint9).
  assert (HlA: Zlength (mi_pub (hcr5_IA x25519 R)) = 32) by apply Hx.
  assert (HlD: Zlength (x25519 (hs_eph (p_hs P)) basepoint9) = 32) by apply Hx.
  assert (HlE: Zlength (map Byte.repr er) = 32) by (rewrite Zlength_map; tauto).
  sep_apply (hcr5_q1b_mstate_joind Tsh (hs_ck (p_hs P)) (hs_hash (p_hs P)) (l_cur L) Lck Lh).
  rewrite (hcr5_q1b_hb_split (x25519 (hs_eph (p_hs P)) basepoint9) (l_ei L)).
  rewrite (hcr5_q1b_hb_split (map Byte.repr er) (l_eraw L)).
  rewrite (hcr5_q1b_mident_split Tsh (hcr5_IA x25519 R) (l_ia L) HlA).
  rewrite (hcr5_q1b_hb_split (mi_pub (hcr5_IA x25519 R)) (field_address t_mident (DOT HR5._pub) (l_ia L))).
  unfold wg_consts. Intros.
  forward_call (gv, Tsh, l_mr L, Tsh, l_cur L, hs_ck (p_hs P), hs_hash (p_hs P), Ews, l_ei L,
                x25519 (hs_eph (p_hs P)) basepoint9, field_address t_mident (DOT HR5._pub) (l_ia L),
                mi_pub (hcr5_IA x25519 R), field_address t_hs (DOT HR5._preshared_key) (hs_addr (hn_p N)),
                hs_psk (p_hs P), l_eraw L, map Byte.repr er).
  sep_apply (hcr5_q1b_hb_join (x25519 (hs_eph (p_hs P)) basepoint9) (l_ei L)).
  sep_apply (hcr5_q1b_hb_join (map Byte.repr er) (l_eraw L)).
  sep_apply (hcr5_q1b_hb_join (mi_pub (hcr5_IA x25519 R)) (field_address t_mident (DOT HR5._pub) (l_ia L))).
  sep_apply (hcr5_q1b_mident_join Tsh (hcr5_IA x25519 R) (l_ia L) HlA).
  sep_apply (hcr5_q1b_hb_out Tsh (x25519 (hs_eph (p_hs P)) basepoint9) (l_ei L)). rewrite HlD.
  sep_apply (hcr5_q1b_hb_out Tsh (map Byte.repr er) (l_eraw L)). rewrite HlE.
  sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P)) (hs_hash (p_hs P))) (l_cur L)).
  sep_apply (hcr5_q1b_peer_fold2 (hn_p N) P Hfp Hok Hfh).
  sep_apply (derives_refl' _ _ (eq_sym Heq)).
  remember (m_create_response_model x25519 aead_enc (hs_ck (p_hs P)) (hs_hash (p_hs P))
              (x25519 (hs_eph (p_hs P)) basepoint9) (mi_pub (hcr5_IA x25519 R)) (hs_psk (p_hs P))
              (map Byte.repr er)) as cr eqn:Hcr.
  forward_if (hcr5_q1b_mid gv L FR R S NS PS head (hn_addr N) T KE m mode).
  { destruct cr as [[[[[E encn] ep] ck2] h2] |]; [| contradiction].
    destruct (hcr5_q1b_cresp_len _ _ _ _ _ _ _ _ _ _ _ Hx Ha (eq_sym Hcr)) as [HlE2 HlN].
    unfold resp_rep. Intros. destruct M as [ty se re eph0 encn0 mac1 mac2].
    destruct H3 as (Hl1 & Hl2 & Hl3 & Hl4); cbn [rm_eph rm_encn rm_mac1 rm_mac2] in *.
    rewrite (hcr5_q1b_resp_split Ews ty se re eph0 encn0 mac1 mac2 m Hl1 Hl2).
    rewrite (hcr5_q1b_mresp_split Tsh E encn ep ck2 h2 (l_mr L) HlE2 HlN). Intros.
    assert_PROP (field_compatible t_resp [] m /\ field_compatible t_mresp [] (l_mr L)) as Hf12.
    { go_lower. saturate_local. apply prop_right. split.
      - match goal with Hc: field_compatible t_resp (DOT HR5._macs) m |- _ =>
          apply field_compatible_cons in Hc; exact (proj2 Hc) end.
      - match goal with Hc: field_compatible t_mresp (DOT HR5._st) (l_mr L) |- _ =>
          apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
    destruct Hf12 as [Hf1 Hf2].
    forward.
    unfold itable. Intros.
    match goal with Hw: itable_wf T |- _ => destruct Hw as (HwL & HwI & HwD & HwS) end.
    assert (HinE: In (hs_addr (hn_p N)) (saddrs (t_D T))).
    { destruct H1 as (_ & Hhs). eapply hcr5_q1b_skipn_in, hcr5_q1b_pool_in; eauto. }
    destruct (hcr5_q1b_focus (t_L T) (t_D T) (hs_addr (hn_p N)) HinE HwS) as (she & E0 & Rst & Hrd & Heq2).
    rewrite Heq2. Intros.
    rewrite <- (hcr5_q1b_entry_fld she (entry_val E0 (succ_in (t_L T) (hs_addr (hn_p N))) (vin (hs_addr (hn_p N)) (t_L T))) (hs_addr (hn_p N)) Hfh).
    forward. forward.
    rewrite (hcr5_q1b_entry_fld she (entry_val E0 (succ_in (t_L T) (hs_addr (hn_p N))) (vin (hs_addr (hn_p N)) (t_L T))) (hs_addr (hn_p N)) Hfh).
    sep_apply (derives_refl' _ _ (eq_sym Heq2)).
    sep_apply (hcr5_q1b_hb_out Ews eph0 (field_address t_resp [StructField HR5._unencrypted_ephemeral] m)).
    rewrite Hl1.
    forward_call (Ews, field_address t_resp [StructField HR5._unencrypted_ephemeral] m, Tsh,
                  field_address t_mresp [StructField HR5._ephemeral] (l_mr L), E).
    { rewrite HlE2. entailer!.
      all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite HlE2. cancel. }
    sep_apply (hcr5_q1b_hb_out Ews encn0 (field_address t_resp [StructField HR5._encrypted_nothing] m)).
    rewrite Hl2.
    forward_call (Ews, field_address t_resp [StructField HR5._encrypted_nothing] m, Tsh,
                  field_address t_mresp [StructField HR5._enc_nothing] (l_mr L), encn).
    { rewrite HlN. entailer!.
      all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite HlN. cancel. }
    sep_apply (hcr5_q1b_mresp_join Tsh E encn ep ck2 h2 (l_mr L) HlE2 HlN).
    sep_apply (hcr5_q1b_resp_join Ews (Int.repr 2) se (e_index E0) E encn mac1 mac2 m HlE2 HlN Hl3 Hl4).
    unfold hcr5_q1b_mid. Exists (mkRM (Int.repr 2) se (e_index E0) E encn mac1 mac2).
    unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs, hcr5_consts, wg_consts, itable; cbn [app].
    entailer!. split; [unfold rm_ok; simpl; auto | unfold itable_wf; auto]. }
  { destruct cr as [[[[[E encn] ep] ck2] h2] |]; [discriminate |].
    forward. unfold hcr5_q1b_mid. Exists M.
    unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs, hcr5_consts, wg_consts; cbn [app].
    Intros ab. match goal with |- context [@data_at HCS Tsh t_mresp ?v (l_mr L)] =>
      sep_apply (@data_at_data_at_ HCS Tsh t_mresp v (l_mr L)) end.
    entailer!. }
  unfold POSTCONDITION, Delta, Delta_specs, abbreviate.
  exact (hcr5_q1b_s2_ok gv L FR R S NS PS head (hn_addr N) T KE m mode (normal_ret_assert FF)).
Qed.

End Q1b.

Lemma hcr5_Q1b_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_SQ1a x25519 gv L FR) hcr5_Q1b
    (overridePost (hcr5_SQ1b x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_SQ1a, hcr5_Delta, hcr5_R, hcr5_Q1b. simplify_func_tycontext. abbreviate_semax.
  Intros R S NS PS head nb T KE m M mode.
  unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app].
  assert (Hna: nb = nullval \/ In nb (map hn_addr NS)) by apply H0.
  forward_if (temp HR5._t'16 (Vint (if Z.eqb mode 0 then Int.zero else if eq_dec nb nullval then Int.zero else Int.one))).
  { forward.
    { destruct Hna as [-> | Hin]; [entailer! |].
      entailer!. pull_left (hnodes_rep4 W (hcr5_head NS) NS).
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      repeat apply sepcon_valid_pointer1. apply hcr5_q1b_node_valid; exact Hin. }
    assert (Hm: mode <> 0) by (intro; subst; contradiction).
    entailer!. rewrite (proj2 (Z.eqb_neq mode 0) Hm).
    destruct (eq_dec nb nullval) as [-> | Hn]; [reflexivity |].
    destruct nb; try contradiction; [simpl in *; subst; contradiction Hn; reflexivity | reflexivity]. }
  { assert (Hm: mode = 0).
    { match goal with Hc: Int.repr mode = Int.repr 0 |- _ => apply (f_equal Int.unsigned) in Hc;
        rewrite !Int.unsigned_repr in Hc by rep_lia; exact Hc
      | Hc: mode = 0 |- _ => exact Hc end. }
    forward. subst mode. entailer!. }
  forward_if.
  { assert (Hm: mode <> 0) by (intro; subst; simpl in *; contradiction).
    assert (Hn: nb <> nullval)
      by (intro; subst; rewrite (proj2 (Z.eqb_neq mode 0) Hm) in *; simpl in *; contradiction).
    eapply semax_pre; [| exact (hcr5_q1b_body_ok gv L FR R S NS PS head nb T KE m M mode (normal_ret_assert FF) HH)].
    unfold hcr5_q1b_pre, hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app]. entailer!. }
  { forward. unfold hcr5_SQ1b. Exists R S NS PS head nb T KE m M.
    unfold hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_world, hcr5_globs; cbn [app]. entailer!. }
Qed.

End Phase.
