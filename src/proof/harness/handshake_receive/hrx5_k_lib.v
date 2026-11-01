(* law handshake_receive: helpers of hrx5_body_k.v (k_initiation,
   k_response): compspecs conversions to the unit's HRX, the peer opened at the handshake fields the builders
   touch, the harness structs / messages field by field, common sub-shares. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
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
Local Open Scope logic.

#[local] Existing Instance HRX.

(* the world's compspecs binder CSw hidden from typeclass resolution (it would be picked over HRX) *)
Definition hrx5_k_hide : Type := compspecs.
Ltac hrx5_k_hide_cs := match goal with C: compspecs |- _ => change hrx5_k_hide in C end.

(* ---------------------------------------------------------------------- *)
(* Helpers: compspecs conversions (Noise.CS / HCS -> HRX)                  *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hrx5_k_cce_N : change_composite_env Noise.CS HRX.
Proof. make_cs_preserve Noise.CS HRX. Defined.
#[local] Instance hrx5_k_cce_H : change_composite_env HCS HRX.
Proof. make_cs_preserve HCS HRX. Defined.

Lemma hrx5_k_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

(* byte arrays are the same in every compspecs (the environment's nondet_bytes is at the world CSw) *)
Lemma hrx5_k_align_tuchar_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuchar n) z -> align_compatible_rec ce2 (tarray tuchar n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma hrx5_k_fc_tuchar_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuchar n) [] p <-> @field_compatible cs2 (tarray tuchar n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (hrx5_k_align_tuchar_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (hrx5_k_align_tuchar_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma hrx5_k_tuchar_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply hrx5_k_fc_tuchar_cs.
Qed.

Lemma hrx5_k_tuchar__cs {cs1 cs2: compspecs} sh n p :
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  unfold data_at_, field_at_, field_at. f_equal. f_equal. apply prop_ext. apply hrx5_k_fc_tuchar_cs.
Qed.

Lemma hrx5_k_hb sh bs p :
  hbytes sh bs p = @data_at HRX sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof. unfold hbytes. apply (@hrx5_k_cs_eq HCS HRX _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hrx5_k_hout sh n p : hout sh n p = @data_at_ HRX sh (tarray tuchar n) p.
Proof.
  unfold hout. rewrite !data_at__eq.
  apply (@hrx5_k_cs_eq HCS HRX _); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hrx5_k_hb_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hrx5_k_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result as an hbytes buffer *)
Lemma hrx5_k_nd (bs: list Z) n p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at HRX Tsh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. rewrite hrx5_k_hb, Zlength_map, Hl, hrx5_k_map_Vint by auto. reflexivity.
Qed.

(* a common sub-share: a byte buffer split along a join_sub *)
Lemma hrx5_k_hsplit sh0 sh bs p : sepalg.join_sub sh0 sh ->
  exists r, hbytes sh bs p = (hbytes sh0 bs p * hbytes r bs p)%logic.
Proof.
  intros [r J]. exists r. unfold hbytes. symmetry. apply data_at_share_join; exact J.
Qed.

Lemma hrx5_k_sub_l sh : sepalg.join_sub (Share.glb Share.Rsh sh) sh.
Proof. apply leq_join_sub, Share.glb_lower2. Qed.

Lemma hrx5_k_sub_w sh shw : writable_share shw -> sepalg.join_sub (Share.glb Share.Rsh sh) shw.
Proof.
  intros [_ Hw]. eapply sepalg.join_sub_trans; [| exact Hw]. apply leq_join_sub, Share.glb_lower1.
Qed.

Lemma hrx5_k_sub_T sh : sepalg.join_sub sh Tsh.
Proof. apply leq_join_sub, Share.top_correct. Qed.

Lemma hrx5_k_rd sh : readable_share sh -> readable_share (Share.glb Share.Rsh sh).
Proof. apply readable_glb. Qed.

Lemma hrx5_k_supd_saddrs {A: Type} (D: list (val * share * A)) a v : saddrs (supd D a v) = saddrs D.
Proof.
  induction D as [| [[x sh] w] D IH]; [reflexivity |].
  simpl. destruct (EqDec_val x a); simpl; [reflexivity | f_equal; exact IH].
Qed.

Lemma hrx5_k_insert_saddrs T a idx : saddrs (t_D (t_insert T a idx)) = saddrs (t_D T).
Proof.
  unfold t_insert, t_set_index. simpl. destruct (t_entry T a); simpl; [| reflexivity].
  apply hrx5_k_supd_saddrs.
Qed.

(* ---------------------------------------------------------------------- *)
(* The peer, opened at the fields k_response touches                        *)
(* ---------------------------------------------------------------------- *)

Ltac hrx5_k_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS HRX _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite hrx5_k_hb, Hl; reflexivity.

Lemma hrx5_k_hs_ck sh H h : Zlength (hs_ck H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h =
  hbytes sh (hs_ck H) (@field_address HRX t_hs (DOT HRC._chaining_key) h).
Proof. hrx5_k_hsf_tac. Qed.
Lemma hrx5_k_hs_hash sh H h : Zlength (hs_hash H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._hash) (bytes (hs_hash H)) h =
  hbytes sh (hs_hash H) (@field_address HRX t_hs (DOT HRC._hash) h).
Proof. hrx5_k_hsf_tac. Qed.
Lemma hrx5_k_hs_eph sh H h : Zlength (hs_eph H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._ephemeral_private) (bytes (hs_eph H)) h =
  hbytes sh (hs_eph H) (@field_address HRX t_hs (DOT HRC._ephemeral_private) h).
Proof. hrx5_k_hsf_tac. Qed.
Lemma hrx5_k_hs_psk sh H h : Zlength (hs_psk H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT I._preshared_key) (bytes (hs_psk H)) h =
  hbytes sh (hs_psk H) (@field_address HRX t_hs (DOT HRC._preshared_key) h).
Proof. hrx5_k_hsf_tac. Qed.
Lemma hrx5_k_hs_state sh H h :
  @field_at Noise.CS sh t_hs (DOT I._state) (Vint (hs_state H)) h =
  @field_at HRX sh t_hs (DOT HRC._state) (Vint (hs_state H)) h.
Proof.
  rewrite (@field_at_change_composite Noise.CS HRX _ sh t_hs (DOT I._state) (Vint (hs_state H)) (Vint (hs_state H))
    (JMeq_refl _)) by reflexivity.
  reflexivity.
Qed.

(* the rest of the peer: neither the state nor the four byte fields read *)
Definition hrx5_k_prest (sh: share) (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS sh t_hs [StructField I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS sh t_hs [StructField I._static_identity] (hs_sid H) h *
   @field_at Noise.CS sh t_hs [StructField I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS sh t_hs [StructField I._remote_ephemeral] (bytes (hs_reph H)) h *
   @field_at Noise.CS sh t_hs [StructField I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS sh t_hs [StructField I._latest_timestamp] (bytes (hs_ts H)) h *
   @field_at Noise.CS sh t_hs [StructField I._remote_index] (Vint (hs_rindex H)) h *
   (EX lk: val, @field_at Noise.CS sh t_hs [StructField I._lock] lk h) *
   spacer sh 36 40 h * spacer sh 300 304 h *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Definition hrx5_k_pok (p: val) (P: peer) : Prop :=
  @field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P) /\ @field_compatible HRX t_hs [] (hs_addr p).

Lemma hrx5_k_peer_open sh p P :
  peer_rep sh p P =
  (!! hrx5_k_pok p P &&
   (@field_at HRX sh t_hs (DOT HRC._state) (Vint (hs_state (p_hs P))) (hs_addr p) *
    hbytes sh (hs_ck (p_hs P)) (@field_address HRX t_hs (DOT HRC._chaining_key) (hs_addr p)) *
    hbytes sh (hs_hash (p_hs P)) (@field_address HRX t_hs (DOT HRC._hash) (hs_addr p)) *
    hbytes sh (hs_eph (p_hs P)) (@field_address HRX t_hs (DOT HRC._ephemeral_private) (hs_addr p)) *
    hbytes sh (hs_psk (p_hs P)) (@field_address HRX t_hs (DOT HRC._preshared_key) (hs_addr p)) *
    hrx5_k_prest sh p P))%logic.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros.
    assert (Hok := H0). destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hrx5_k_hs_ck sh (p_hs P) (hs_addr p) L7), (hrx5_k_hs_hash sh (p_hs P) (hs_addr p) L6),
      (hrx5_k_hs_eph sh (p_hs P) (hs_addr p) L1), (hrx5_k_hs_psk sh (p_hs P) (hs_addr p) L5),
      hrx5_k_hs_state.
    unfold hrx5_k_prest. Intros lk.
    assert_PROP (@field_compatible HRX t_hs (DOT HRC._state) (hs_addr p)) as Hf by entailer!.
    apply andp_right.
    + apply prop_right. split; [exact H | split; [exact Hok |]].
      apply field_compatible_cons in Hf. destruct Hf as [_ Hf]. exact Hf.
    + Exists lk. cancel.
  - Intros. destruct H as (Hfp & Hok & Hfh). pose proof Hok as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold peer_rep, hs_rep, hrx5_k_prest.
    rewrite (hrx5_k_hs_ck sh (p_hs P) (hs_addr p) L7), (hrx5_k_hs_hash sh (p_hs P) (hs_addr p) L6),
      (hrx5_k_hs_eph sh (p_hs P) (hs_addr p) L1), (hrx5_k_hs_psk sh (p_hs P) (hs_addr p) L5),
      hrx5_k_hs_state.
    Intros lk. Exists lk. entailer!.
Qed.

Lemma hrx5_k_prest_state sh p P s :
  hrx5_k_prest sh p (p_set_hs P (hs_set_state (p_hs P) s)) = hrx5_k_prest sh p P.
Proof. reflexivity. Qed.

Lemma hrx5_k_pok_state p P s : hrx5_k_pok p P -> hrx5_k_pok p (p_set_hs P (hs_set_state (p_hs P) s)).
Proof. intros (A & B & C). split; [exact A | split; [exact B | exact C]]. Qed.

(* ---------------------------------------------------------------------- *)
(* The pool entry of the handshake, the harness structs, the message       *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_k_entry_cs sh E n h p :
  @data_at Noise.CS sh t_entry_s (entry_val E n h) p = @data_at HRX sh t_entry_s (entry_val E n h) p.
Proof. apply (@hrx5_k_cs_eq Noise.CS HRX _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hrx5_k_split {A: Type} (D: list (val * share * A)) a :
  In a (saddrs D) -> exists D1 sh E D2, D = D1 ++ (a, sh, E) :: D2.
Proof.
  unfold saddrs. rewrite in_map_iff. intros [[[x sh] E] [Hx Hin]]. simpl in Hx. subst x.
  apply in_split in Hin. destruct Hin as [l1 [l2 ->]]. eauto.
Qed.

Lemma hrx5_k_focus L D e :
  In e (saddrs D) -> Forall (fun x => match x with (_, sh, _) => writable_share sh end) D ->
  exists sh E Rst, readable_share sh /\
    iter_sepcon (pool_item_rep L) D =
    (@data_at HRX sh t_entry_s (entry_val E (succ_in L e) (vin e L)) e * Rst)%logic.
Proof.
  intros Ha HF. destruct (hrx5_k_split D e Ha) as (D1 & sh & E & D2 & ->).
  exists sh, E, (iter_sepcon (pool_item_rep L) (D1 ++ D2)). split.
  - rewrite Forall_forall in HF. specialize (HF (e, sh, E) ltac:(apply in_or_app; right; left; reflexivity)).
    apply writable_readable; exact HF.
  - rewrite !iter_sepcon_app. simpl. unfold pool_item_rep at 2, entry_at. rewrite hrx5_k_entry_cs.
    rewrite <- !sepcon_assoc, (sepcon_comm (iter_sepcon _ D1)). reflexivity.
Qed.

(* the entry as a field of the handshake *)
Lemma hrx5_k_entry_fld sh (v: @reptype HRX t_entry_s) h :
  @field_compatible HRX t_hs [] h ->
  @field_at HRX sh t_hs (DOT HRC._entry) v h = @data_at HRX sh t_entry_s v h.
Proof.
  intros Hf. rewrite field_at_data_at. unfold field_address. rewrite if_true.
  - simpl. rewrite isptr_offset_val_zero by (destruct Hf; auto). reflexivity.
  - apply field_compatible_cons; split; [unfold in_members; simpl; auto 20 | exact Hf].
Qed.

Lemma hrx5_k_mstate_split sh p :
  @data_at_ HRX sh (Tstruct HRC._m_state noattr) p =
  (hout sh 32 (@field_address HRX t_mstate [StructField HRC._ck] p) *
   hout sh 32 (@field_address HRX t_mstate [StructField HRC._h] p))%logic.
Proof.
  rewrite !hrx5_k_hout. rewrite data_at__eq. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HRC._ck]), (field_at_data_at sh t_mstate [StructField HRC._h]).
  rewrite <- !data_at__eq. reflexivity.
Qed.

Lemma hrx5_k_mstate_join sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  (hbytes sh ck (@field_address HRX t_mstate [StructField HRC._ck] p) *
   hbytes sh h (@field_address HRX t_mstate [StructField HRC._h] p) |--
   @data_at HCS sh t_mstate (mstate_val ck h) p)%logic.
Proof.
  intros H1 H2. rewrite !hrx5_k_hb, H1, H2.
  rewrite (@hrx5_k_cs_eq HCS HRX _ sh t_mstate (mstate_val ck h) (mstate_val ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HRC._ck]), (field_at_data_at sh t_mstate [StructField HRC._h]).
  apply derives_refl.
Qed.

Lemma hrx5_k_mstate_cs sh p : @data_at_ HRX sh (Tstruct HRC._m_state noattr) p = @data_at_ HCS sh t_mstate p.
Proof.
  rewrite !data_at__eq. symmetry. apply (@hrx5_k_cs_eq HCS HRX _); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hrx5_k_mresp_cs0 sh p : @data_at_ HRX sh (Tstruct HRC._m_response noattr) p = @data_at_ HCS sh t_mresp p.
Proof.
  rewrite !data_at__eq. symmetry. apply (@hrx5_k_cs_eq HCS HRX _); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hrx5_k_mresp_split sh E encn ep ck h p :
  Zlength E = 32 -> Zlength encn = 16 ->
  @data_at HCS sh t_mresp (mresp_val E encn ep ck h) p =
  (hbytes sh E (@field_address HRX t_mresp [StructField HRC._ephemeral] p) *
   hbytes sh encn (@field_address HRX t_mresp [StructField HRC._enc_nothing] p) *
   @field_at HRX sh t_mresp [StructField HRC._eph_priv] (bytes ep) p *
   @field_at HRX sh t_mresp [StructField HRC._st] (bytes ck, bytes h) p)%logic.
Proof.
  intros H1 H2.
  rewrite (@hrx5_k_cs_eq HCS HRX _ sh t_mresp (mresp_val E encn ep ck h) (mresp_val E encn ep ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hrx5_k_hb, H1, H2. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mresp [StructField HRC._ephemeral]).
  rewrite (field_at_data_at sh t_mresp [StructField HRC._enc_nothing]). apply pred_ext; cancel.
Qed.

Lemma hrx5_k_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (@field_at HRX sh t_mident [StructField HRC._priv] (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (@field_address HRX t_mident [StructField HRC._pub] p) *
   @field_at HRX sh t_mident [StructField HRC._ok] (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.
Proof.
  intros Hl.
  rewrite (@hrx5_k_cs_eq HCS HRX _ sh t_mident (mident_val I) (mident_val I) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite hrx5_k_hb, Hl. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident [StructField HRC._pub]). apply pred_ext; cancel.
Qed.

Lemma hrx5_k_resp_split sh ty se re eph encn mac1 mac2 m :
  Zlength eph = 32 -> Zlength encn = 16 ->
  @data_at Noise.CS sh t_resp (resp_val (mkRM ty se re eph encn mac1 mac2)) m =
  (@field_at HRX sh t_resp [StructField HRC._header] (Vint ty) m *
   @field_at HRX sh t_resp [StructField HRC._sender_index] (Vint se) m *
   @field_at HRX sh t_resp [StructField HRC._receiver_index] (Vint re) m *
   hbytes sh eph (@field_address HRX t_resp [StructField HRC._unencrypted_ephemeral] m) *
   hbytes sh encn (@field_address HRX t_resp [StructField HRC._encrypted_nothing] m) *
   @field_at HRX sh t_resp [StructField HRC._macs] (bytes mac1, bytes mac2) m)%logic.
Proof.
  intros H1 H2.
  rewrite (@hrx5_k_cs_eq Noise.CS HRX _ sh t_resp (resp_val _) (resp_val (mkRM ty se re eph encn mac1 mac2)) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hrx5_k_hb, H1, H2. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_resp [StructField HRC._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_resp [StructField HRC._encrypted_nothing]). apply pred_ext; cancel.
Qed.

Lemma hrx5_k_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros Hl. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

Lemma hrx5_k_cresp_len x25519 aead_enc aead_dec CK H EI SI PSK ERAW E encn ep ck h :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  m_create_response_model x25519 aead_enc CK H EI SI PSK ERAW = Some (E, encn, ep, ck, h) ->
  Zlength E = 32 /\ Zlength encn = 16.
Proof.
  intros Hx Ha Hm. unfold m_create_response_model in Hm.
  repeat match type of Hm with context [if ?c then _ else _] => destruct c end; try discriminate.
  inversion Hm; subst. rewrite (aead_enc_length _ _ Ha). auto.
Qed.

