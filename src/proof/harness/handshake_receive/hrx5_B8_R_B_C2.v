(* law handshake_receive: B8 branch R segment B: C2 = CHECK(state, remote_ephemeral, hash, chaining_key, remote_index) of the failed allocation.
*)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_B_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---- helpers: port of consume_response_any Q5 A3 (hcr5_q5_A3.v, renamed hcr5_q5_A3_ -> hrx5_B8RBC2_) ---- *)
(* the accepted peer after consume_response, its reference count back (as in rw_PS W1 of FF) *)
Definition hrx5_B8RBC2_put (P: peer) (M: resp_msg) (ck h: list byte) : peer :=
  p_set_refs (hrx5cr_new P M ck h) (p_refs P).

#[local] Instance hrx5_B8RBC2_cce_N : change_composite_env Noise.CS W_handshake_receive.
Proof. make_cs_preserve Noise.CS W_handshake_receive. Defined.
#[local] Instance hrx5_B8RBC2_cce_H : change_composite_env HCS W_handshake_receive.
Proof. make_cs_preserve HCS W_handshake_receive. Defined.

Lemma hrx5_B8RBC2_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

Lemma hrx5_B8RBC2_hb_W sh bs p :
  hbytes sh bs p = @data_at W_handshake_receive sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof. unfold hbytes. apply (@hrx5_B8RBC2_cs_eq HCS W_handshake_receive _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hrx5_B8RBC2_bytes_eqb_refl A : bytes_eqb A A = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec A A); congruence. Qed.

(* byte fields of the handshake as hbytes, scalar fields at the world's compspecs *)
Ltac hrx5_B8RBC2_hsf_tac :=
  intros Hl; match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_handshake_receive _ sh t gfs v v (JMeq_refl v)) by reflexivity end;
  rewrite field_at_data_at; rewrite hrx5_B8RBC2_hb_W, Hl; reflexivity.

Lemma hrx5_B8RBC2_hs_reph sh H h : Zlength (hs_reph H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._remote_ephemeral) (bytes (hs_reph H)) h =
  hbytes sh (hs_reph H) (@field_address W_handshake_receive t_hs (DOT HRM._remote_ephemeral) h).
Proof. hrx5_B8RBC2_hsf_tac. Qed.
Lemma hrx5_B8RBC2_hs_hash sh H h : Zlength (hs_hash H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._hash) (bytes (hs_hash H)) h =
  hbytes sh (hs_hash H) (@field_address W_handshake_receive t_hs (DOT HRM._hash) h).
Proof. hrx5_B8RBC2_hsf_tac. Qed.
Lemma hrx5_B8RBC2_hs_ck sh H h : Zlength (hs_ck H) = 32 ->
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._chaining_key) (bytes (hs_ck H)) h =
  hbytes sh (hs_ck H) (@field_address W_handshake_receive t_hs (DOT HRM._chaining_key) h).
Proof. hrx5_B8RBC2_hsf_tac. Qed.

Lemma hrx5_B8RBC2_hs_state sh x h :
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._state) (Vint x) h =
  @field_at W_handshake_receive sh t_hs (DOT HRM._state) (Vint x) h.
Proof.
  match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_handshake_receive _ sh t gfs v v (JMeq_refl v)) by reflexivity end.
  reflexivity.
Qed.
Lemma hrx5_B8RBC2_hs_rindex sh x h :
  @field_at Noise.CS sh t_hs (DOT prot_repr3.I._remote_index) (Vint x) h =
  @field_at W_handshake_receive sh t_hs (DOT HRM._remote_index) (Vint x) h.
Proof.
  match goal with |- @field_at _ ?sh ?t ?gfs ?v ?h = _ =>
    rewrite (@field_at_change_composite Noise.CS W_handshake_receive _ sh t gfs v v (JMeq_refl v)) by reflexivity end.
  reflexivity.
Qed.

(* field_compatible of a field from that of another field of the same struct *)
Ltac hrx5_B8RBC2_fc_tac :=
  match goal with |- field_compatible ?t (DOT ?f) ?p =>
    match goal with Hf: field_compatible t (DOT _) p |- _ =>
      apply field_compatible_cons in Hf; destruct Hf as [_ Hf];
      apply field_compatible_cons; split; [unfold in_members; simpl; tauto | exact Hf] end end.

(* the peer at a in the list after an update *)
Lemma hrx5_B8RBC2_peers PS a sh P Q : sfind PS a = Some (sh, P) ->
  peers_rep (supd PS a Q) = (peer_rep sh a Q * peers_rep (sdel PS a))%logic.
Proof.
  induction PS as [| [[x sh0] w] PS IH]; simpl; intros Hf; [discriminate |].
  unfold peers_rep in *. destruct (EqDec_val x a) as [Ex | Hne]; [subst x |].
  - inversion Hf; subst. simpl. reflexivity.
  - simpl. rewrite IH by exact Hf. unfold peer_item_rep.
    rewrite <- !sepcon_assoc, (sepcon_comm (peer_rep sh0 x w)). reflexivity.
Qed.

(* a peer, opened at the five handshake fields A3 reads (the rest kept in one predicate) *)
Definition hrx5_B8RBC2_rest (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at Noise.CS Ews t_peer [StructField prot_repr3.I._device] (p_device P) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep Ews (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._last_initiation_consumption] (Vlong (hs_lic H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._static_identity] (hs_sid H) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._ephemeral_private] (bytes (hs_eph H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._remote_static] (bytes (hs_rstatic H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._precomputed_static_static] (bytes (hs_ss H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._preshared_key] (bytes (hs_psk H)) h *
   @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._latest_timestamp] (bytes (hs_ts H)) h *
   (EX lk: val, @field_at Noise.CS Ews t_hs [StructField prot_repr3.I._lock] lk h) *
   spacer Ews 36 40 h * spacer Ews 300 304 h *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep Ews (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._refcount] (Vint (p_refs P)) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS Ews t_peer [StructField prot_repr3.I._pubkey_next] (p_pknext P) p *
   spacer Ews 9 16 p * spacer Ews 476 480 p)%logic.

Definition hrx5_B8RBC2_five (p: val) (P: peer) : mpred :=
  let H := p_hs P in let h := hs_addr p in
  (@field_at W_handshake_receive Ews t_hs (DOT HRM._state) (Vint (hs_state H)) h *
   hbytes Ews (hs_reph H) (@field_address W_handshake_receive t_hs (DOT HRM._remote_ephemeral) h) *
   hbytes Ews (hs_hash H) (@field_address W_handshake_receive t_hs (DOT HRM._hash) h) *
   hbytes Ews (hs_ck H) (@field_address W_handshake_receive t_hs (DOT HRM._chaining_key) h) *
   @field_at W_handshake_receive Ews t_hs (DOT HRM._remote_index) (Vint (hs_rindex H)) h)%logic.

Lemma hrx5_B8RBC2_open p P :
  peer_rep Ews p P =
  (!! (@field_compatible Noise.CS t_peer [] p /\ hs_ok (p_hs P)) &&
   (hrx5_B8RBC2_five p P * hrx5_B8RBC2_rest p P))%logic.
Proof.
  apply pred_ext.
  - unfold peer_rep, hs_rep. Intros.
    assert (Hok := H0). destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    rewrite (hrx5_B8RBC2_hs_reph Ews (p_hs P) (hs_addr p) L3), (hrx5_B8RBC2_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hrx5_B8RBC2_hs_ck Ews (p_hs P) (hs_addr p) L7), hrx5_B8RBC2_hs_state, hrx5_B8RBC2_hs_rindex.
    unfold hrx5_B8RBC2_five, hrx5_B8RBC2_rest. Intros lk.
    apply andp_right; [apply prop_right; auto | Exists lk; cancel].
  - Intros. destruct H0 as (L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8).
    unfold peer_rep, hs_rep, hrx5_B8RBC2_five, hrx5_B8RBC2_rest.
    rewrite (hrx5_B8RBC2_hs_reph Ews (p_hs P) (hs_addr p) L3), (hrx5_B8RBC2_hs_hash Ews (p_hs P) (hs_addr p) L6),
      (hrx5_B8RBC2_hs_ck Ews (p_hs P) (hs_addr p) L7), hrx5_B8RBC2_hs_state, hrx5_B8RBC2_hs_rindex.
    Intros lk. Exists lk. entailer!. unfold hs_ok; auto 10.
Qed.

(* the message, opened at the two fields A3 reads *)
Definition hrx5_B8RBC2_mrest (sh: share) (m: val) (M: resp_msg) : mpred :=
  (@field_at W_handshake_receive sh t_resp [StructField HRM._header] (Vint (rm_type M)) m *
   @field_at W_handshake_receive sh t_resp [StructField HRM._receiver_index] (Vint (rm_receiver M)) m *
   hbytes sh (rm_encn M) (@field_address W_handshake_receive t_resp [StructField HRM._encrypted_nothing] m) *
   @field_at W_handshake_receive sh t_resp [StructField HRM._macs] (bytes (rm_mac1 M), bytes (rm_mac2 M)) m)%logic.

Lemma hrx5_B8RBC2_resp_open sh M m : rm_ok M ->
  resp_rep sh m M =
  (hbytes sh (rm_eph M) (@field_address W_handshake_receive t_resp [StructField HRM._unencrypted_ephemeral] m) *
   @field_at W_handshake_receive sh t_resp [StructField HRM._sender_index] (Vint (rm_sender M)) m *
   hrx5_B8RBC2_mrest sh m M)%logic.
Proof.
  intros Hok. assert (Hok' := Hok). destruct Hok' as (H1 & H2 & _).
  unfold resp_rep, hrx5_B8RBC2_mrest. rewrite prop_true_andp by exact Hok.
  rewrite (@hrx5_B8RBC2_cs_eq Noise.CS W_handshake_receive _ sh t_resp (resp_val M) (resp_val M) m)
    by (apply JMeq_refl || prove_cs_preserve_type).
  rewrite !hrx5_B8RBC2_hb_W, H1, H2. unfold resp_val. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_resp [StructField HRM._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_resp [StructField HRM._encrypted_nothing]). apply pred_ext; cancel.
Qed.

(* the model's state st, opened at its two fields *)
Lemma hrx5_B8RBC2_mstate sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  @data_at HCS sh t_mstate (mstate_val ck h) p =
  (hbytes sh ck (@field_address W_handshake_receive t_mstate [StructField HRM._ck] p) *
   hbytes sh h (@field_address W_handshake_receive t_mstate [StructField HRM._h] p))%logic.
Proof.
  intros H1 H2. rewrite !hrx5_B8RBC2_hb_W, H1, H2.
  rewrite (@hrx5_B8RBC2_cs_eq HCS W_handshake_receive _ sh t_mstate (mstate_val ck h) (mstate_val ck h) p)
    by (apply JMeq_refl || prove_cs_preserve_type).
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mstate [StructField HRM._ck]), (field_at_data_at sh t_mstate [StructField HRM._h]).
  reflexivity.
Qed.

(* folding back: the accepted peer (its five fields at their known values), the message, st, the list *)
Lemma hrx5_B8RBC2_fold a P M ck h :
  @field_compatible Noise.CS t_peer [] a -> hs_ok (p_hs (hrx5_B8RBC2_put P M ck h)) ->
  (@field_at W_handshake_receive Ews t_hs (DOT HRM._state) (Vint (Int.repr 4)) (hs_addr a) *
   hbytes Ews (rm_eph M) (@field_address W_handshake_receive t_hs (DOT HRM._remote_ephemeral) (hs_addr a)) *
   hbytes Ews h (@field_address W_handshake_receive t_hs (DOT HRM._hash) (hs_addr a)) *
   hbytes Ews ck (@field_address W_handshake_receive t_hs (DOT HRM._chaining_key) (hs_addr a)) *
   @field_at W_handshake_receive Ews t_hs (DOT HRM._remote_index) (Vint (rm_sender M)) (hs_addr a) *
   hrx5_B8RBC2_rest a (hrx5_B8RBC2_put P M ck h)
   |-- peer_rep Ews a (hrx5_B8RBC2_put P M ck h))%logic.
Proof.
  intros H1 H2. rewrite (hrx5_B8RBC2_open a (hrx5_B8RBC2_put P M ck h)).
  apply andp_right; [apply prop_right; auto |]. unfold hrx5_B8RBC2_five. apply derives_refl.
Qed.

Lemma hrx5_B8RBC2_resp_fold sh M m : rm_ok M ->
  (hbytes sh (rm_eph M) (@field_address W_handshake_receive t_resp [StructField HRM._unencrypted_ephemeral] m) *
   @field_at W_handshake_receive sh t_resp [StructField HRM._sender_index] (Vint (rm_sender M)) m *
   hrx5_B8RBC2_mrest sh m M |-- resp_rep sh m M)%logic.
Proof. intros Hok. rewrite (hrx5_B8RBC2_resp_open sh M m Hok). apply derives_refl. Qed.

Lemma hrx5_B8RBC2_mstate_fold sh ck h p : Zlength ck = 32 -> Zlength h = 32 ->
  (hbytes sh ck (@field_address W_handshake_receive t_mstate [StructField HRM._ck] p) *
   hbytes sh h (@field_address W_handshake_receive t_mstate [StructField HRM._h] p)
   |-- @data_at HCS sh t_mstate (mstate_val ck h) p)%logic.
Proof. intros H1 H2. rewrite (hrx5_B8RBC2_mstate sh ck h p H1 H2). apply derives_refl. Qed.

Lemma hrx5_B8RBC2_peers_fold PS a sh P Q : sfind PS a = Some (sh, P) ->
  (peer_rep sh a Q * peers_rep (sdel PS a) |-- peers_rep (supd PS a Q))%logic.
Proof. intros Hf. rewrite (hrx5_B8RBC2_peers PS a sh P Q Hf). apply derives_refl. Qed.

Lemma hrx5_B8RBC2_sfind : forall PS a sh P, NoDup (map peer_addr4 PS) -> In (a, sh, P) PS ->
  sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[x sh0] w] PS IH]; simpl; intros a sh P Hnd Hin; [contradiction|].
  inv Hnd. destruct Hin as [Heq | Hin].
  - inv Heq. rewrite if_true by auto. reflexivity.
  - rewrite if_false; [eauto|]. intros ->. apply H1.
    change a with (peer_addr4 (a, sh, P)). apply in_map; auto.
Qed.

Lemma hrx5_B8RBC2_st x25519 aead_dec R T PS M st a P ck h :
  hrx5_fwd (obj_bytes (OResp M)) = true ->
  hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h) ->
  hrx5_st_rep x25519 aead_dec R T PS (OResp M) st = @data_at HCS Tsh t_mstate (mstate_val ck h) st.
Proof. intros H1 H2. unfold hrx5_st_rep. rewrite H1, H2. reflexivity. Qed.

Lemma hrx5_B8RB_C2_ok : hrx5_B8RB_C2_stmt.
Proof.
  intros Espec x25519 aead_enc aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp img tg ai ar d a P M ck h j HY.
  cbv beta zeta delta [hrx5_B8RB_Sf hrx5_B8R_St].
  unfold hrx5_Delta, hrx5_B8RB_C2.
  unfold hrx5_B8RB_G, hrx5_B8RB_FF, hrx5_B8R_tl, hrx5_lvars, hrx5_rest, hrx5_cglobs, hrx5_scr5; cbn [app].
  match goal with |- context [hrx5_RB ?x1 ?x2 ?x3 ?x4] => destruct (hrx5_RB x1 x2 x3 x4) as [r1 r2 r3 r4] end.
  cbn [overridePost].
  abbreviate_semax.
  Intros.
  subst o.
  pose proof H0 as Hinv; destruct Hinv as (_ & _ & Hnd & _).
  assert (Hin: In (a, Ews, P) PS) by (rewrite <- H13; apply Znth_In; exact H12).
  pose proof (hrx5_B8RBC2_sfind PS a Ews P Hnd Hin) as Hsf.
  unfold rxw_rep. rewrite H27.
  change (p_set_refs (hrx5cr_new P M ck h) (p_refs P)) with (hrx5_B8RBC2_put P M ck h).
  rewrite (hrx5_B8RBC2_peers PS a Ews P (hrx5_B8RBC2_put P M ck h) Hsf), hrx5_B8RBC2_open. Intros.
  match goal with Hx: hs_ok _ |- _ => rename Hx into Hok end.
  match goal with Hx: @field_compatible Noise.CS t_peer [] a |- _ => rename Hx into Hfc end.
  change (obj_rep dp (OResp M)) with (@malloc_token W Ews t_resp dp * resp_rep Ews dp M).
  rewrite (hrx5_B8RBC2_resp_open Ews M dp H3).
  rewrite (hrx5_B8RBC2_st x25519 aead_dec R T PS M (l_st L) a P ck h H8 H11).
  assert (Hok' := Hok). unfold hrx5_B8RBC2_put, hrx5cr_new, p_set_refs, p_set_hs in Hok'. cbn [p_hs] in Hok'.
  destruct Hok' as (_ & _ & Lre & _ & _ & Lh & Lck & _). cbn [hs_reph hs_hash hs_ck] in Lre, Lh, Lck.
  rewrite (hrx5_B8RBC2_mstate Tsh ck h (l_st L) Lck Lh).
  change (hrx5_ptrs dp (OResp M)) with [temp HM._buf nullval; temp HM._mi nullval; temp HM._mr dp; temp HM._mc nullval].
  cbn [app].
  unfold hrx5_B8RBC2_five. repeat flatten_sepcon_in_SEP.
  replace (hs_state (p_hs (hrx5_B8RBC2_put P M ck h))) with (Int.repr 4) by reflexivity.
  replace (hs_reph (p_hs (hrx5_B8RBC2_put P M ck h))) with (rm_eph M) by reflexivity.
  replace (hs_hash (p_hs (hrx5_B8RBC2_put P M ck h))) with h by reflexivity.
  replace (hs_ck (p_hs (hrx5_B8RBC2_put P M ck h))) with ck by reflexivity.
  replace (hs_rindex (p_hs (hrx5_B8RBC2_put P M ck h))) with (rm_sender M) by reflexivity.
  assert_PROP (isptr (field_address t_mstate (DOT HRM._h) (l_st L)) /\
               isptr (field_address t_mstate (DOT HRM._ck) (l_st L))) as Hst by (unfold hbytes; entailer!).
  destruct Hst as [Hsth Hstck]. rewrite isptr_field_address_lemma in Hsth, Hstck.
  freeze FR1 := - (@field_at W_handshake_receive Ews t_hs (DOT HRM._state) _ _)
    (hbytes Ews _ (@field_address W_handshake_receive t_hs (DOT HRM._remote_ephemeral) _))
    (hbytes Ews _ (@field_address W_handshake_receive t_hs (DOT HRM._hash) _))
    (hbytes Ews _ (@field_address W_handshake_receive t_hs (DOT HRM._chaining_key) _))
    (@field_at W_handshake_receive Ews t_hs (DOT HRM._remote_index) _ _)
    (hbytes Ews _ (@field_address W_handshake_receive t_resp _ _))
    (@field_at W_handshake_receive Ews t_resp (DOT HRM._sender_index) _ _)
    (hbytes Tsh _ (@field_address W_handshake_receive t_mstate (DOT HRM._ck) _))
    (hbytes Tsh _ (@field_address W_handshake_receive t_mstate (DOT HRM._h) _)).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre break: Pre end.
  - apply ENTAIL_refl.
  - forward.
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'152 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { forward_call (Ews, field_address t_hs (DOT HRM._remote_ephemeral) (hs_addr a), rm_eph M,
                    Ews, field_address t_resp (DOT HRM._unencrypted_ephemeral) dp, rm_eph M).
      { entailer!. rewrite Lre. unfold field_address. rewrite !if_true. reflexivity. all: hrx5_B8RBC2_fc_tac. }
      rewrite hrx5_B8RBC2_bytes_eqb_refl.
      forward. entailer!. }
    { exfalso; auto. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'154 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { forward_call (Ews, field_address t_hs (DOT HRM._hash) (hs_addr a), h,
                    Tsh, field_address t_mstate (DOT HRM._h) (l_st L), h).
      { entailer!. rewrite Lh. unfold field_address. rewrite !if_true by (auto; hrx5_B8RBC2_fc_tac). reflexivity. }
      rewrite hrx5_B8RBC2_bytes_eqb_refl.
      forward. entailer!. }
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'156 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { forward_call (Ews, field_address t_hs (DOT HRM._chaining_key) (hs_addr a), ck,
                    Tsh, field_address t_mstate (DOT HRM._ck) (l_st L), ck).
      { entailer!. rewrite Lck. unfold field_address. rewrite !if_true by (auto; hrx5_B8RBC2_fc_tac). reflexivity. }
      rewrite hrx5_B8RBC2_bytes_eqb_refl.
      forward. entailer!. }
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    match goal with |- semax _ (PROPx ?P (LOCALx ?Q (SEPx ?R))) _ _ =>
      forward_if (PROPx P (LOCALx (temp HRM._t'158 (Vint (Int.repr 1)) :: Q) (SEPx R))) end.
    { forward. forward. forward. rewrite Int.eq_true. entailer!. }
    { exfalso; match goal with Hc: _ = Int.zero |- _ => exact (Int.one_not_zero Hc) end. }
    forward_if True.
    { exfalso; match goal with Hc: _ = Int.zero |- _ => rewrite ?Int.eq_true in Hc; exact (Int.one_not_zero Hc) end. }
    { forward. entailer!. }
    forward.
    entailer!.
  - thaw FR1.
    sep_apply (hrx5_B8RBC2_fold a P M ck h Hfc Hok).
    sep_apply (hrx5_B8RBC2_resp_fold Ews M dp H3).
    sep_apply (hrx5_B8RBC2_mstate_fold Tsh ck h (l_st L) Lck Lh).
    sep_apply (hrx5_B8RBC2_peers_fold PS a Ews P (hrx5_B8RBC2_put P M ck h) Hsf).
    rewrite (hrx5_B8RBC2_st x25519 aead_dec R T PS M (l_st L) a P ck h H8 H11).
    unfold rxw_rep. rewrite H27.
    change (p_set_refs (hrx5cr_new P M ck h) (p_refs P)) with (hrx5_B8RBC2_put P M ck h).
    change (obj_rep dp (OResp M)) with (@malloc_token W Ews t_resp dp * resp_rep Ews dp M).
    change (hrx5_ptrs dp (OResp M)) with [temp HM._buf nullval; temp HM._mi nullval; temp HM._mr dp; temp HM._mc nullval].
    cbn [app].
    entailer!.
Qed.
