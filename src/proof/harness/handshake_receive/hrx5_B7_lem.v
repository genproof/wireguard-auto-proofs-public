(*
   - the message object as bytes: the cookie
     message's image, obj_rep = token * bytes_at;
   - the reflexivity of the comparisons (bytes_eqb, skb_eqb, dev_eqb);
   - the receive model keeps the device's pointers and the peers' addresses. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Local Open Scope logic.

Section CK.
#[local] Existing Instance Cookie.CS.

Lemma hrx5_b7_cmsg_eq sh m M :
  field_compatible t_cmsg [] m -> cm_ok M ->
  data_at sh t_cmsg (cmsg_val M) m = bytes_at sh (cookie_msg_bytes M) m.
Proof.
  intros FC OK.
  unfold_data_at (data_at sh t_cmsg (cmsg_val M) m).
  assert (EH: forall v, field_at sh t_cmsg (DOT cookie.code._header) v m =
                        field_at sh t_cmsg (DOT cookie.code._header DOT cookie.code._type) v m).
  { intros v. apply pred_ext. unfold_field_at 1%nat. cancel. unfold_field_at 2%nat. cancel. }
  rewrite EH; clear EH.
  rewrite !field_at_data_at.
  rewrite !field_address_offset by auto with field_compatible.
  simpl nested_field_type. simpl nested_field_offset. unfold cmsg_val; simpl fst; simpl snd.
  rewrite (prot_rep3_u32_le sh (cm_type M) (offset_val 0 m))
    by exact (field_compatible_nested_field t_cmsg (DOT cookie.code._header DOT cookie.code._type) m
                ltac:(auto with field_compatible)).
  rewrite (prot_rep3_u32_le sh (cm_receiver M) (offset_val 4 m))
    by exact (field_compatible_nested_field t_cmsg (DOT cookie.code._receiver_index) m
                ltac:(auto with field_compatible)).
  rewrite !(@data_at_tarray_tuchar_cs Cookie.CS Noise.CS).
  destruct OK as (L1 & L2).
  assert (FB: forall k len, 0 <= k -> 0 <= len -> k + len <= 64 ->
            @field_compatible Noise.CS (tarray tuchar len) [] (offset_val k m)).
  { intros k len Hk Hl Hn. apply (@field_compatible_tarray_tuchar_cs Cookie.CS Noise.CS).
    apply (prot_rep3_fc_bytes t_cmsg); auto. }
  replace (bytes_at sh (cookie_msg_bytes M) m) with (bytes_at sh (cookie_msg_bytes M) (offset_val 0 m))
    by (rewrite isptr_offset_val_zero by (destruct FC; auto); reflexivity).
  unfold cookie_msg_bytes.
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_type M)) _ m 0 4 4 60)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  rewrite (prot_rep3_bytes_app_at sh (le32 (cm_receiver M)) _ m 4 8 4 56)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  rewrite (prot_rep3_bytes_app_at sh (cm_nonce M) _ m 8 32 24 32)
    by (rewrite ?Zlength_app, ?prot_rep3_le32_len, ?L1, ?L2; try lia; apply FB; lia).
  unfold bytes_at. rewrite !prot_rep3_le32_len, L1, L2. reflexivity.
Qed.

End CK.

(* ---------------------------------------------------------------------- *)
(* the message object = its malloc token * its bytes                      *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_b7_tok (dp: val) (o: hrx5_obj) : mpred :=
  match o with
  | OBuf b => @malloc_token W Ews (tarray tuchar (Zlength b)) dp
  | OInit _ => @malloc_token W Ews t_init dp
  | OResp _ => @malloc_token W Ews t_resp dp
  | OCookie _ => @malloc_token W Ews t_cmsg dp
  end.

Lemma hrx5_b7_obj_len o : obj_ok o -> 0 <= Zlength (obj_bytes o) <= Int.max_unsigned.
Proof.
  destruct o as [b|M|M|M]; simpl; intros OK.
  - pose proof (Zlength_nonneg b). lia.
  - destruct OK as (L1&L2&L3&L4&L5). unfold init_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5. rep_lia.
  - destruct OK as (L1&L2&L3&L4). unfold resp_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4. rep_lia.
  - destruct OK as (L1&L2). unfold cookie_msg_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2. rep_lia.
Qed.

Lemma hrx5_b7_obj_open dp o : obj_ok o -> malloc_compatible (Zlength (obj_bytes o)) dp ->
  obj_rep dp o = hrx5_b7_tok dp o * bytes_at Ews (obj_bytes o) dp.
Proof.
  intros OK MC. destruct o as [b|M|M|M]; simpl in MC |- *; [reflexivity | | |].
  - unfold init_rep. rewrite prop_true_andp by exact OK.
    rewrite prot_rep3_init_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (sizeof t_init) with (Zlength (init_bytes M)); [exact MC |].
    destruct OK as (L1&L2&L3&L4&L5). unfold init_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5. reflexivity.
  - unfold resp_rep. rewrite prop_true_andp by exact OK.
    rewrite prot_rep3_resp_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (sizeof t_resp) with (Zlength (resp_bytes M)); [exact MC |].
    destruct OK as (L1&L2&L3&L4). unfold resp_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4. reflexivity.
  - unfold cmsg_rep. rewrite prop_true_andp by exact OK.
    rewrite hrx5_b7_cmsg_eq; [reflexivity | | exact OK].
    apply malloc_compatible_field_compatible; [| reflexivity | reflexivity].
    replace (@sizeof Cookie.CS t_cmsg) with (Zlength (cookie_msg_bytes M)); [exact MC |].
    destruct OK as (L1&L2). unfold cookie_msg_bytes.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2. reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the comparisons are reflexive                                           *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_b7_bytes_eqb_refl (a: list byte) : bytes_eqb a a = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec a a); [reflexivity | contradiction]. Qed.

Lemma hrx5_b7_veqb_refl (x: val) : veqb x x = true.
Proof. unfold veqb. destruct (eq_dec x x); [reflexivity | contradiction]. Qed.

Lemma hrx5_b7_skb_eqb_refl (s: skb) : skb_eqb s s = true.
Proof.
  unfold skb_eqb. rewrite hrx5_b7_veqb_refl, Int.eq_true, Z.eqb_refl, !hrx5_b7_bytes_eqb_refl. reflexivity.
Qed.

Lemma hrx5_b7_dev_eqb_refl (D: device) (h: val) : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hrx5_b7_veqb_refl, !hrx5_b7_bytes_eqb_refl, Int64.eq_true, Bool.eqb_reflx.
  reflexivity.
Qed.

(* ---------------------------------------------------------------------- *)
(* the receive model keeps the device's pointers and the peers' addresses *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_b7_ash (x: val * share * peer) : val * share := match x with (a, sh, _) => (a, sh) end.

Lemma hrx5_b7_supd_ash (PS: list (val * share * peer)) a P :
  map hrx5_b7_ash (supd PS a P) = map hrx5_b7_ash PS.
Proof.
  induction PS as [| [[x sh] Q] PS IH]; simpl; [reflexivity |].
  match goal with |- context [if ?c then _ else _] => destruct c end; simpl; [reflexivity | f_equal; exact IH].
Qed.

Section Rx.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Definition hrx5_b7_dptrs (D: device) : list val := [d_dev D; d_ptab D; d_itab D; cc_dev (d_cc D)].

Lemma hrx5_b7_rx_dev W q sp s msg d :
  hrx5_b7_dptrs (rw_D (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = hrx5_b7_dptrs (rw_D W).
Proof.
  unfold rx_model. destruct (hrx5_fwd msg); [| reflexivity].
  unfold rx_packet.
  destruct (Int.eq (hrx5_tw msg) (Int.repr 3)); [reflexivity |].
  assert (HV: forall CC b n r, cc_dev (snd (validate_model CC s msg b n (s_rlallow (rw_S W)) r)) = cc_dev CC).
  { intros CC b n r. unfold validate_model, checker_rotate.
    repeat (simpl; match goal with |- context [if ?c then _ else _] => destruct c end); reflexivity. }
  match goal with |- context [validate_model ?CC ?s ?m ?ul ?n ?rl ?r] =>
    pose proof (HV CC ul n r) as HV1; destruct (validate_model CC s m ul n rl r) as [v CC1] eqn:EV end.
  simpl in HV1 |- *.
  destruct (rx_consumes _ v).
  - destruct (Int.eq (hrx5_tw msg) Int.one).
    + match goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[a P1]|] end;
        unfold hrx5_b7_dptrs; simpl; rewrite HV1; reflexivity.
    + match goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[a P1]|] end;
        unfold hrx5_b7_dptrs; simpl; rewrite HV1; reflexivity.
  - destruct (rx_needs_cookie _ v); unfold hrx5_b7_dptrs; simpl; [| rewrite HV1; reflexivity].
    unfold mc_res, message_create_model, checker_rotate. simpl.
    match goal with |- context [if ?c then _ else _] => destruct c end; simpl; rewrite HV1; reflexivity.
Qed.

Lemma hrx5_b7_rx_ash W q sp s msg d :
  map hrx5_b7_ash (rw_PS (rx_model x25519 aead_dec xaead_enc xaead_dec W q sp s msg d)) = map hrx5_b7_ash (rw_PS W).
Proof.
  unfold rx_model. destruct (hrx5_fwd msg); [| reflexivity].
  unfold rx_packet.
  destruct (Int.eq (hrx5_tw msg) (Int.repr 3)).
  { simpl. unfold peers_after. destruct (mcons_res _ _ _ _ _) as [[a P]|]; [apply hrx5_b7_supd_ash | reflexivity]. }
  destruct (rx_consumes _ _).
  - destruct (Int.eq (hrx5_tw msg) Int.one).
    + match goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[a P1]|] end;
        simpl; [apply hrx5_b7_supd_ash | reflexivity].
    + match goal with |- context [match ?x with Some _ => _ | None => _ end] => destruct x as [[a P1]|] end;
        simpl; [apply hrx5_b7_supd_ash | reflexivity].
  - destruct (rx_needs_cookie _ _); reflexivity.
Qed.

End Rx.

(* the public-key table's head is NULL or a peer's address *)
Lemma hrx5_b7_head_in head (PS: list (val * share * peer)) :
  pk_chain head PS -> head = nullval \/ In head (map peer_addr4 PS).
Proof.
  intros H. destruct PS as [| [[a sh] P] PS]; simpl in H |- *; [left; exact H |].
  destruct H as [E _]. right. left. symmetry. exact E.
Qed.

Lemma hrx5_b7_ash_addrs (PS PS': list (val * share * peer)) :
  map hrx5_b7_ash PS' = map hrx5_b7_ash PS -> map peer_addr4 PS' = map peer_addr4 PS.
Proof.
  revert PS. induction PS' as [| [[a sh] P] PS' IH]; intros [| [[b sh2] Q] PS] E; simpl in E |- *;
    try discriminate; [reflexivity |].
  injection E as E1 E2 E3. subst. f_equal. apply IH. exact E3.
Qed.

Lemma hrx5_b7_ash_ews (PS PS': list (val * share * peer)) :
  map hrx5_b7_ash PS' = map hrx5_b7_ash PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS ->
  Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS'.
Proof.
  revert PS. induction PS' as [| [[a sh] P] PS' IH]; intros [| [[b sh2] Q] PS] E F; simpl in E |- *;
    try discriminate; [constructor |].
  injection E as E1 E2 E3. subst. inversion F; subst. constructor; [reflexivity | eapply IH; eauto].
Qed.

(* the objects lent to dev_same / skb_same (hcl5_P8.v's recipe) *)
Lemma hrx5_b7_vok PS : Forall (fun x => match x with (_, sh, _) => sh = Ews end) PS -> vobj_ok (VPeers PS).
Proof. intros H. cbn. eapply Forall_impl; [|exact H]. intros [[a sh] P] ->. apply writable_readable, writable_Ews. Qed.

Lemma hrx5_b7_vo2 tab T PS : (itable Tsh tab T * peers_rep PS)%logic = vobjs W [VItab Tsh tab T; VPeers PS].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_b7_vo1 sh bs a : bytes_at sh bs a = vobjs W [VBytes sh bs a].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_b7_dpre wg it pt head T' PS' D :
  d_dev D = nullval -> cc_dev (d_cc D) = wg -> d_ptab D = pt -> d_itab D = it ->
  head = nullval \/ In head (map peer_addr4 PS') ->
  Forall (vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS'])) (dev_ptrs D head D head).
Proof.
  intros H1 H2 H3 H4 Hh. unfold dev_ptrs. rewrite H1, H2, H3, H4.
  assert (Hv: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) head).
  { destruct Hh as [-> | Hh]; [left; reflexivity|]. right. cbn. right; right; right.
    apply in_or_app; right. rewrite app_nil_r. exact Hh. }
  assert (Hn: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) nullval) by (left; reflexivity).
  assert (Hw: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) wg) by (right; left; reflexivity).
  assert (Hp: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) pt) by (right; right; left; reflexivity).
  assert (Hi: vp_ok ([wg; pt] ++ vobjs_addrs [VItab Tsh it T'; VPeers PS']) it)
    by (right; right; right; left; reflexivity).
  apply Forall_cons; [exact Hn|]. apply Forall_cons; [exact Hn|].
  apply Forall_cons; [exact Hw|]. apply Forall_cons; [exact Hw|].
  apply Forall_cons; [exact Hp|]. apply Forall_cons; [exact Hp|].
  apply Forall_cons; [exact Hi|]. apply Forall_cons; [exact Hi|].
  apply Forall_cons; [exact Hv|]. apply Forall_cons; [exact Hv|]. apply Forall_nil.
Qed.

(* the skb local at the world's compspecs (hrx5_B3.v's recipe) *)
#[local] Instance hrx5_b7_cce : change_composite_env Cookie.CS W_handshake_receive.
Proof. make_cs_preserve Cookie.CS W_handshake_receive. Defined.

Lemma hrx5_b7_skb_cs sh (s: skb) p :
  @data_at Cookie.CS sh t_skb (skb_val s) p = @data_at W_handshake_receive sh t_skb (skb_val s) p.
Proof.
  unfold skb_val.
  apply (f_equal (fun f => f p)).
  apply (@data_at_change_composite Cookie.CS W_handshake_receive _); [apply JMeq_refl | reflexivity].
Qed.

(* hbytes (HCS) = bytes_at (Noise.CS) *)
Lemma hrx5_b7_hbytes sh bs p : bytes_at sh bs p = hbytes sh bs p.
Proof. unfold bytes_at, hbytes. apply data_at_tarray_tuchar_cs. Qed.

(* the empty kind-0 packet (draw_size() = 0, malloc(0)): lent to skb_same as common4 v4.1's VTok *)
Lemma hrx5_b7_empty o : obj_ok o -> Zlength (obj_bytes o) = 0 -> o = OBuf [].
Proof.
  destruct o as [b|M|M|M]; simpl; intros OK Hz.
  - apply Zlength_nil_inv in Hz. subst. reflexivity.
  - exfalso. destruct OK as (L1&L2&L3&L4&L5). unfold init_bytes in Hz.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4, L5 in Hz. lia.
  - exfalso. destruct OK as (L1&L2&L3&L4). unfold resp_bytes in Hz.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2, L3, L4 in Hz. lia.
  - exfalso. destruct OK as (L1&L2). unfold cookie_msg_bytes in Hz.
    rewrite !Zlength_app, !prot_rep3_le32_len, L1, L2 in Hz. lia.
Qed.

Lemma hrx5_b7_vot dp : @malloc_token W Ews (tarray tuchar 0) dp = vobjs W [VTok Ews (tarray tuchar 0) dp].
Proof. unfold vobjs. cbn. rewrite sepcon_emp. reflexivity. Qed.

Lemma hrx5_b7_vtok_ok dp : vobj_ok (VTok Ews (tarray tuchar 0) dp).
Proof. cbn. intros cs. lia. Qed.
