(* hc_pieces3, group msg: common.h bodies, proved once at a small compspecs with the callee context
   of hc3_ctx.v.  One lemma per function (per law where the Clight
   reads a renamed constant). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common.hc3_cs.
Require Import WgNoise.proof.harness.common.hc3_ctx.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code WgNoise.harness.x_consume_response_any.code
        WgNoise.harness.x_keypairs.code WgNoise.harness.x_create_any.code WgNoise.harness.x_replay.code
        WgNoise.harness.x_cookie_mac.code WgNoise.harness.x_consume_initiation_any.code.
Require WgNoise.contracts.x_cookie_reply.

Module FH := WgNoise.harness.x_handshake.code.
Module FK := WgNoise.harness.x_cookie_reply.code.
Module FR := WgNoise.harness.x_consume_response_any.code.

(* every lemma takes all the section variables and hypotheses (a stable signature for the assembly) *)
#[local] Set Default Proof Using "All".

(* ---------------------------------------------------------------------------------------------- *)
(* byte buffers: splitting an output image, merging the written pieces                            *)
(* ---------------------------------------------------------------------------------------------- *)

Local Open Scope logic.

Lemma hc3b_msg_actr: forall (ce: composite_env) n z, align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma hc3b_msg_fc_cs: forall {cs1 cs2: compspecs} n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (hc3b_msg_actr (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (hc3b_msg_actr (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hc3b_msg_data_at_cs: forall {cs1 cs2: compspecs} sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hc3b_msg_fc_cs.
Qed.

Lemma hc3b_msg_data_at__cs: forall {cs1 cs2: compspecs} sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hc3b_msg_data_at_cs.
Qed.

Lemma hc3b_msg_fc_suffix: forall N p k n,
  @field_compatible HCS (tarray tuchar N) [] p -> 0 <= k -> 0 <= n -> k + n <= N ->
  @field_compatible HCS (tarray tuchar n) [] (offset_val k p).
Proof.
  intros N p k n FC Hk Hn Hkn.
  destruct p; try (destruct FC; contradiction).
  destruct FC as [_ [_ [SZ [_ _]]]].
  unfold size_compatible in SZ. simpl sizeof in SZ. rewrite Z.max_r in SZ by lia.
  pose proof (Ptrofs.unsigned_range i).
  split; [simpl; auto|]. split; [reflexivity|].
  split; [|split; [|simpl; auto]].
  - unfold size_compatible, offset_val. simpl sizeof. rewrite Z.max_r by lia.
    rewrite Ptrofs.add_unsigned, Ptrofs.unsigned_repr by (rewrite Ptrofs.unsigned_repr; rep_lia).
    rewrite Ptrofs.unsigned_repr; rep_lia.
  - unfold align_compatible, offset_val. apply hc3b_msg_actr.
Qed.

Lemma hc3b_msg_hout_take0: forall sh N p k n m,
  @field_compatible HCS (tarray tuchar N) [] p -> 0 <= k -> 0 <= n -> 0 <= m -> k + n + m <= N ->
  hout sh (n + m) (offset_val k p) |-- hout sh n (offset_val k p) * hout sh m (offset_val (k + n) p).
Proof.
  intros sh N p k n m FC Hk Hn Hm HN.
  assert (FC2 := hc3b_msg_fc_suffix N p k (n + m) FC Hk ltac:(lia) ltac:(lia)).
  unfold hout.
  rewrite (split2_data_at__Tarray_tuchar sh (n + m) n (offset_val k p)) by (auto; try lia; destruct FC2; auto).
  change (Tarray tuchar (n + m) noattr) with (tarray tuchar (n + m)).
  rewrite arr_field_address0 by (auto; lia).
  replace (n + m - n) with m by lia. rewrite offset_offset_val. simpl sizeof. rewrite Z.mul_1_l. apply derives_refl.
Qed.

Lemma hc3b_msg_hbytes_merge: forall sh N p k A B,
  @field_compatible HCS (tarray tuchar N) [] p -> 0 <= k -> k + Zlength A + Zlength B <= N ->
  hbytes sh A (offset_val k p) * hbytes sh B (offset_val (k + Zlength A) p) |-- hbytes sh (A ++ B) (offset_val k p).
Proof.
  intros sh N p k A B FC Hk HN.
  assert (FC2 := hc3b_msg_fc_suffix N p k (Zlength A + Zlength B) FC Hk ltac:(list_solve) ltac:(lia)).
  unfold hbytes, bytes. rewrite map_app, Zlength_app.
  erewrite (@split2_data_at_Tarray_app HCS (Zlength A) (Zlength A + Zlength B) sh tuchar (map Vubyte A) (map Vubyte B));
    [| rewrite Zlength_map; reflexivity | rewrite Zlength_map; lia].
  rewrite arr_field_address0 by (auto; list_solve).
  replace (Zlength A + Zlength B - Zlength A) with (Zlength B) by lia.
  rewrite offset_offset_val. simpl sizeof. rewrite Z.mul_1_l. apply derives_refl.
Qed.

Lemma hc3b_msg_hout_take: forall sh N p k n m r k',
  @field_compatible HCS (tarray tuchar N) [] p -> 0 <= k -> 0 <= n -> 0 <= m -> k + n + m <= N ->
  r = n + m -> k' = k + n ->
  hout sh r (offset_val k p) |-- hout sh n (offset_val k p) * hout sh m (offset_val k' p).
Proof. intros; subst; eapply hc3b_msg_hout_take0; eauto. Qed.

Lemma hc3b_msg_merge: forall sh N p k k' A B,
  @field_compatible HCS (tarray tuchar N) [] p -> 0 <= k -> k + Zlength A + Zlength B <= N -> k' = k + Zlength A ->
  hbytes sh A (offset_val k p) * hbytes sh B (offset_val k' p) |-- hbytes sh (A ++ B) (offset_val k p).
Proof. intros; subst; eapply hc3b_msg_hbytes_merge; eauto. Qed.

Lemma hc3b_msg_le32_len: forall v, Zlength (le32 v) = 4.
Proof. intros. reflexivity. Qed.

Lemma hc3b_msg_nd: forall {cs: compspecs} sh n bs p, Zlength bs = n ->
  Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at cs sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p = hbytes sh (map Byte.repr bs) p.
Proof.
  intros cs sh n bs p L F. unfold hbytes. rewrite Zlength_map, L.
  rewrite (@hc3b_msg_data_at_cs cs HCS). f_equal.
  unfold bytes. rewrite map_map. apply map_ext_in. intros a Ha.
  rewrite Forall_forall in F. specialize (F a Ha).
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

Section MI.
#[local] Existing Instance CSmi.
#[local] Instance hc3b_msg_cc_mi : change_composite_env Noise.CS CSmi. make_cs_preserve Noise.CS CSmi. Defined.

Lemma hc3b_msg_init_eq: forall sh m M, im_ok M ->
  @data_at Noise.CS sh t_init (init_val M) m =
  field_at sh t_init (DOT FH._header DOT FH._type) (Vint (im_type M)) m *
  field_at sh t_init (DOT FH._sender_index) (Vint (im_sender M)) m *
  hbytes sh (im_eph M) (field_address t_init (DOT FH._unencrypted_ephemeral) m) *
  hbytes sh (im_encs M) (field_address t_init (DOT FH._encrypted_static) m) *
  hbytes sh (im_enct M) (field_address t_init (DOT FH._encrypted_timestamp) m) *
  hbytes sh (im_mac1 M) (field_address t_init (DOT FH._macs DOT FH._mac1) m) *
  hbytes sh (im_mac2 M) (field_address t_init (DOT FH._macs DOT FH._mac2) m).
Proof.
  intros sh m M OK.
  erewrite (@data_at_change_composite Noise.CS CSmi _ sh t_init _ _ (JMeq_refl _)) by reflexivity.
  unfold_data_at (data_at _ _ _ m).
  unfold init_val; cbn [fst snd].
  unfold_field_at 1%nat. unfold_field_at 6%nat.
  rewrite !field_at_data_at. unfold hbytes.
  destruct OK as (L1&L2&L3&L4&L5). rewrite L1,L2,L3,L4,L5.
  rewrite <- !(@hc3b_msg_data_at_cs CSmi HCS).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_msg_init_eq_: forall sh m,
  @data_at_ Noise.CS sh t_init m =
  field_at_ sh t_init (DOT FH._header DOT FH._type) m *
  field_at_ sh t_init (DOT FH._sender_index) m *
  data_at_ sh (tarray tuchar 32) (field_address t_init (DOT FH._unencrypted_ephemeral) m) *
  data_at_ sh (tarray tuchar 48) (field_address t_init (DOT FH._encrypted_static) m) *
  data_at_ sh (tarray tuchar 28) (field_address t_init (DOT FH._encrypted_timestamp) m) *
  data_at_ sh (tarray tuchar 16) (field_address t_init (DOT FH._macs DOT FH._mac1) m) *
  data_at_ sh (tarray tuchar 16) (field_address t_init (DOT FH._macs DOT FH._mac2) m).
Proof.
  intros sh m.
  rewrite (@data_at__change_composite Noise.CS CSmi _ sh t_init) by reflexivity.
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ m).
  unfold_field_at 1%nat. unfold_field_at 6%nat.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at. rewrite !data_at__eq.
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_msg_init_out: forall sh i M, @field_compatible HCS (tarray tuchar 148) [] i -> im_ok M ->
  hout sh 148 i |-- hout sh 4 i * hout sh 4 (offset_val 4 i) * hout sh (Zlength (im_eph M)) (offset_val 8 i) *
    hout sh (Zlength (im_encs M)) (offset_val 40 i) * hout sh (Zlength (im_enct M)) (offset_val 88 i) *
    hout sh (Zlength (im_mac1 M)) (offset_val 116 i) * hout sh (Zlength (im_mac2 M)) (offset_val 132 i).
Proof.
  intros sh i M FC (L1&L2&L3&L4&L5). rewrite L1,L2,L3,L4,L5.
  assert (P: isptr i) by (destruct FC; auto).
  rewrite <- (isptr_offset_val_zero i P) at 1.
  sep_apply (hc3b_msg_hout_take sh 148 i 0 4 144 148 4); try lia.
  sep_apply (hc3b_msg_hout_take sh 148 i 4 4 140 144 8); try lia.
  sep_apply (hc3b_msg_hout_take sh 148 i 8 32 108 140 40); try lia.
  sep_apply (hc3b_msg_hout_take sh 148 i 40 48 60 108 88); try lia.
  sep_apply (hc3b_msg_hout_take sh 148 i 88 28 32 60 116); try lia.
  sep_apply (hc3b_msg_hout_take sh 148 i 116 16 16 32 132); try lia.
  rewrite (isptr_offset_val_zero i P). cancel.
Qed.

Lemma hc3b_msg_init_in: forall sh i M, @field_compatible HCS (tarray tuchar 148) [] i -> im_ok M ->
  hbytes sh (le32 (im_type M)) i * hbytes sh (le32 (im_sender M)) (offset_val 4 i) *
  hbytes sh (im_eph M) (offset_val 8 i) * hbytes sh (im_encs M) (offset_val 40 i) *
  hbytes sh (im_enct M) (offset_val 88 i) * hbytes sh (im_mac1 M) (offset_val 116 i) *
  hbytes sh (im_mac2 M) (offset_val 132 i) |-- hbytes sh (init_bytes M) i.
Proof.
  intros sh i M FC (L1&L2&L3&L4&L5).
  assert (P: isptr i) by (destruct FC; auto).
  replace (hbytes sh (init_bytes M) i) with (hbytes sh (init_bytes M) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  replace (hbytes sh (le32 (im_type M)) i) with (hbytes sh (le32 (im_type M)) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  unfold init_bytes.
  sep_apply (hc3b_msg_merge sh 148 i 116 132 (im_mac1 M) (im_mac2 M)); try lia.
  sep_apply (hc3b_msg_merge sh 148 i 88 116 (im_enct M) (im_mac1 M ++ im_mac2 M)); try list_solve.
  sep_apply (hc3b_msg_merge sh 148 i 40 88 (im_encs M) (im_enct M ++ im_mac1 M ++ im_mac2 M)); try list_solve.
  sep_apply (hc3b_msg_merge sh 148 i 8 40 (im_eph M) (im_encs M ++ im_enct M ++ im_mac1 M ++ im_mac2 M)); try list_solve.
  sep_apply (hc3b_msg_merge sh 148 i 4 8 (le32 (im_sender M)) (im_eph M ++ im_encs M ++ im_enct M ++ im_mac1 M ++ im_mac2 M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  sep_apply (hc3b_msg_merge sh 148 i 0 4 (le32 (im_type M)) (le32 (im_sender M) ++ im_eph M ++ im_encs M ++ im_enct M ++ im_mac1 M ++ im_mac2 M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  apply derives_refl.
Qed.
End MI.

Section MR.
#[local] Existing Instance CSmr.
#[local] Instance hc3b_msg_cc_mr : change_composite_env Noise.CS CSmr. make_cs_preserve Noise.CS CSmr. Defined.

Lemma hc3b_msg_resp_eq: forall sh m M, rm_ok M ->
  @data_at Noise.CS sh t_resp (resp_val M) m =
  field_at sh t_resp (DOT FH._header DOT FH._type) (Vint (rm_type M)) m *
  field_at sh t_resp (DOT FH._sender_index) (Vint (rm_sender M)) m *
  field_at sh t_resp (DOT FH._receiver_index) (Vint (rm_receiver M)) m *
  hbytes sh (rm_eph M) (field_address t_resp (DOT FH._unencrypted_ephemeral) m) *
  hbytes sh (rm_encn M) (field_address t_resp (DOT FH._encrypted_nothing) m) *
  hbytes sh (rm_mac1 M) (field_address t_resp (DOT FH._macs DOT FH._mac1) m) *
  hbytes sh (rm_mac2 M) (field_address t_resp (DOT FH._macs DOT FH._mac2) m).
Proof.
  intros sh m M OK.
  erewrite (@data_at_change_composite Noise.CS CSmr _ sh t_resp _ _ (JMeq_refl _)) by reflexivity.
  unfold_data_at (data_at _ _ _ m).
  unfold resp_val; cbn [fst snd].
  unfold_field_at 1%nat. unfold_field_at 6%nat.
  rewrite !field_at_data_at. unfold hbytes.
  destruct OK as (L1&L2&L3&L4). rewrite L1,L2,L3,L4.
  rewrite <- !(@hc3b_msg_data_at_cs CSmr HCS).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_msg_resp_eq_: forall sh m,
  @data_at_ Noise.CS sh t_resp m =
  field_at_ sh t_resp (DOT FH._header DOT FH._type) m *
  field_at_ sh t_resp (DOT FH._sender_index) m *
  field_at_ sh t_resp (DOT FH._receiver_index) m *
  data_at_ sh (tarray tuchar 32) (field_address t_resp (DOT FH._unencrypted_ephemeral) m) *
  data_at_ sh (tarray tuchar 16) (field_address t_resp (DOT FH._encrypted_nothing) m) *
  data_at_ sh (tarray tuchar 16) (field_address t_resp (DOT FH._macs DOT FH._mac1) m) *
  data_at_ sh (tarray tuchar 16) (field_address t_resp (DOT FH._macs DOT FH._mac2) m).
Proof.
  intros sh m.
  rewrite (@data_at__change_composite Noise.CS CSmr _ sh t_resp) by reflexivity.
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ m).
  unfold_field_at 1%nat. unfold_field_at 6%nat.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at. rewrite !data_at__eq.
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_msg_resp_out: forall sh i M, @field_compatible HCS (tarray tuchar 92) [] i -> rm_ok M ->
  hout sh 92 i |-- hout sh 4 i * hout sh 4 (offset_val 4 i) * hout sh 4 (offset_val 8 i) *
    hout sh (Zlength (rm_eph M)) (offset_val 12 i) * hout sh (Zlength (rm_encn M)) (offset_val 44 i) *
    hout sh (Zlength (rm_mac1 M)) (offset_val 60 i) * hout sh (Zlength (rm_mac2 M)) (offset_val 76 i).
Proof.
  intros sh i M FC (L1&L2&L3&L4). rewrite L1,L2,L3,L4.
  assert (P: isptr i) by (destruct FC; auto).
  rewrite <- (isptr_offset_val_zero i P) at 1.
  sep_apply (hc3b_msg_hout_take sh 92 i 0 4 88 92 4); try lia.
  sep_apply (hc3b_msg_hout_take sh 92 i 4 4 84 88 8); try lia.
  sep_apply (hc3b_msg_hout_take sh 92 i 8 4 80 84 12); try lia.
  sep_apply (hc3b_msg_hout_take sh 92 i 12 32 48 80 44); try lia.
  sep_apply (hc3b_msg_hout_take sh 92 i 44 16 32 48 60); try lia.
  sep_apply (hc3b_msg_hout_take sh 92 i 60 16 16 32 76); try lia.
  rewrite (isptr_offset_val_zero i P). cancel.
Qed.

Lemma hc3b_msg_resp_in: forall sh i M, @field_compatible HCS (tarray tuchar 92) [] i -> rm_ok M ->
  hbytes sh (le32 (rm_type M)) i * hbytes sh (le32 (rm_sender M)) (offset_val 4 i) *
  hbytes sh (le32 (rm_receiver M)) (offset_val 8 i) *
  hbytes sh (rm_eph M) (offset_val 12 i) * hbytes sh (rm_encn M) (offset_val 44 i) *
  hbytes sh (rm_mac1 M) (offset_val 60 i) * hbytes sh (rm_mac2 M) (offset_val 76 i)
  |-- hbytes sh (resp_bytes M) i.
Proof.
  intros sh i M FC (L1&L2&L3&L4).
  assert (P: isptr i) by (destruct FC; auto).
  replace (hbytes sh (resp_bytes M) i) with (hbytes sh (resp_bytes M) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  replace (hbytes sh (le32 (rm_type M)) i) with (hbytes sh (le32 (rm_type M)) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  unfold resp_bytes.
  sep_apply (hc3b_msg_merge sh 92 i 60 76 (rm_mac1 M) (rm_mac2 M)); try lia.
  sep_apply (hc3b_msg_merge sh 92 i 44 60 (rm_encn M) (rm_mac1 M ++ rm_mac2 M)); try list_solve.
  sep_apply (hc3b_msg_merge sh 92 i 12 44 (rm_eph M) (rm_encn M ++ rm_mac1 M ++ rm_mac2 M)); try list_solve.
  sep_apply (hc3b_msg_merge sh 92 i 8 12 (le32 (rm_receiver M)) (rm_eph M ++ rm_encn M ++ rm_mac1 M ++ rm_mac2 M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  sep_apply (hc3b_msg_merge sh 92 i 4 8 (le32 (rm_sender M)) (le32 (rm_receiver M) ++ rm_eph M ++ rm_encn M ++ rm_mac1 M ++ rm_mac2 M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  sep_apply (hc3b_msg_merge sh 92 i 0 4 (le32 (rm_type M)) (le32 (rm_sender M) ++ le32 (rm_receiver M) ++ rm_eph M ++ rm_encn M ++ rm_mac1 M ++ rm_mac2 M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  apply derives_refl.
Qed.
End MR.

Local Notation hc3b_msg_KCS := WgNoise.contracts.x_cookie_reply.Harness.CS.

Section MC.
#[local] Existing Instance hc3b_msg_KCS.
#[local] Instance hc3b_msg_cc_mc : change_composite_env Cookie.CS hc3b_msg_KCS. make_cs_preserve Cookie.CS hc3b_msg_KCS. Defined.

Lemma hc3b_msg_cookie_eq: forall sh m M, cm_ok M ->
  @data_at Cookie.CS sh t_cmsg (cmsg_val M) m =
  field_at sh t_cmsg (DOT FK._header DOT FK._type) (Vint (cm_type M)) m *
  field_at sh t_cmsg (DOT FK._receiver_index) (Vint (cm_receiver M)) m *
  hbytes sh (cm_nonce M) (field_address t_cmsg (DOT FK._nonce) m) *
  hbytes sh (cm_enc M) (field_address t_cmsg (DOT FK._encrypted_cookie) m).
Proof.
  intros sh m M OK.
  erewrite (@data_at_change_composite Cookie.CS hc3b_msg_KCS _ sh t_cmsg _ _ (JMeq_refl _)) by reflexivity.
  unfold_data_at (data_at _ _ _ m).
  unfold cmsg_val; cbn [fst snd].
  unfold_field_at 1%nat.
  rewrite !field_at_data_at. unfold hbytes.
  destruct OK as (L1&L2). rewrite L1,L2.
  rewrite <- !(@hc3b_msg_data_at_cs hc3b_msg_KCS HCS).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma hc3b_msg_cookie_eq_: forall sh m,
  @data_at_ Cookie.CS sh t_cmsg m =
  field_at_ sh t_cmsg (DOT FK._header DOT FK._type) m *
  field_at_ sh t_cmsg (DOT FK._receiver_index) m *
  data_at_ sh (tarray tuchar 24) (field_address t_cmsg (DOT FK._nonce) m) *
  data_at_ sh (tarray tuchar 32) (field_address t_cmsg (DOT FK._encrypted_cookie) m).
Proof.
  intros sh m.
  rewrite (@data_at__change_composite Cookie.CS hc3b_msg_KCS _ sh t_cmsg) by reflexivity.
  rewrite data_at__eq. unfold_data_at (data_at _ _ _ m).
  unfold_field_at 1%nat.
  rewrite !field_at_data_at. unfold field_at_. rewrite !field_at_data_at. rewrite !data_at__eq.
  rewrite !sepcon_assoc. reflexivity.
Qed.
End MC.

Lemma hc3b_msg_cookie_out: forall sh i M, @field_compatible HCS (tarray tuchar 64) [] i -> cm_ok M ->
  hout sh 64 i |-- hout sh 4 i * hout sh 4 (offset_val 4 i) *
    hout sh (Zlength (cm_nonce M)) (offset_val 8 i) * hout sh (Zlength (cm_enc M)) (offset_val 32 i).
Proof.
  intros sh i M FC (L1&L2). rewrite L1,L2.
  assert (P: isptr i) by (destruct FC; auto).
  rewrite <- (isptr_offset_val_zero i P) at 1.
  sep_apply (hc3b_msg_hout_take sh 64 i 0 4 60 64 4); try lia.
  sep_apply (hc3b_msg_hout_take sh 64 i 4 4 56 60 8); try lia.
  sep_apply (hc3b_msg_hout_take sh 64 i 8 24 32 56 32); try lia.
  rewrite (isptr_offset_val_zero i P). cancel.
Qed.

Lemma hc3b_msg_cookie_in: forall sh i M, @field_compatible HCS (tarray tuchar 64) [] i -> cm_ok M ->
  hbytes sh (le32 (cm_type M)) i * hbytes sh (le32 (cm_receiver M)) (offset_val 4 i) *
  hbytes sh (cm_nonce M) (offset_val 8 i) * hbytes sh (cm_enc M) (offset_val 32 i)
  |-- hbytes sh (cookie_msg_bytes M) i.
Proof.
  intros sh i M FC (L1&L2).
  assert (P: isptr i) by (destruct FC; auto).
  replace (hbytes sh (cookie_msg_bytes M) i) with (hbytes sh (cookie_msg_bytes M) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  replace (hbytes sh (le32 (cm_type M)) i) with (hbytes sh (le32 (cm_type M)) (offset_val 0 i))
    by (rewrite isptr_offset_val_zero; auto).
  unfold cookie_msg_bytes.
  sep_apply (hc3b_msg_merge sh 64 i 8 32 (cm_nonce M) (cm_enc M)); try lia.
  sep_apply (hc3b_msg_merge sh 64 i 4 8 (le32 (cm_receiver M)) (cm_nonce M ++ cm_enc M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  sep_apply (hc3b_msg_merge sh 64 i 0 4 (le32 (cm_type M)) (le32 (cm_receiver M) ++ cm_nonce M ++ cm_enc M));
    try (rewrite ?Zlength_app, ?hc3b_msg_le32_len; lia).
  apply derives_refl.
Qed.

Section Bodies.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Hypothesis X25519: x25519_props x25519.
Hypothesis AEAD: aead_props aead_enc aead_dec.
Hypothesis XAEAD: xaead_props xaead_enc xaead_dec.

#[local] Existing Instance CSmi.

Lemma hc3_body_init_img :
  @semax_body [] (hc3_G_init_img) CSmi FH.f_init_img (init_img_spec).
Proof.
  start_function.
  unfold init_rep. Intros.
  rewrite hc3b_msg_init_eq by auto.
  assert_PROP (@field_compatible HCS (tarray tuchar 148) [] i) by (unfold hout; entailer!).
  sep_apply (hc3b_msg_init_out shi i M); auto.
  repeat flatten_sepcon_in_SEP.
  pose proof H as (L1&L2&L3&L4&L5).
  assert (Pi: isptr i) by (destruct H0; auto).
  assert_PROP (field_compatible t_init [] m) as FCm
    by (entailer!; match goal with H: field_compatible t_init (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  forward.
  forward_call (shi, i, im_type M).
  forward.
  forward_call (shi, offset_val 4 i, im_sender M).
  forward_call (shi, offset_val 8 i, shm, field_address t_init (DOT FH._unencrypted_ephemeral) m, im_eph M).
  { entailer!. simpl. rewrite L1. rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity. }
  forward_call (shi, offset_val 40 i, shm, field_address t_init (DOT FH._encrypted_static) m, im_encs M).
  { entailer!. simpl. rewrite L2. rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity. }
  forward_call (shi, offset_val 88 i, shm, field_address t_init (DOT FH._encrypted_timestamp) m, im_enct M).
  { entailer!. simpl. rewrite L3. rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity. }
  forward_call (shi, offset_val 116 i, shm, field_address t_init (DOT FH._macs DOT FH._mac1) m, im_mac1 M).
  { entailer!. simpl. rewrite L4. rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity. }
  forward_call (shi, offset_val 132 i, shm, field_address t_init (DOT FH._macs DOT FH._mac2) m, im_mac2 M).
  { entailer!. simpl. rewrite L5. rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity. }
  sep_apply (hc3b_msg_init_in shi i M); auto.
  unfold init_rep. rewrite hc3b_msg_init_eq by auto.
  entailer!.
Qed.

Lemma hc3_body_resp_img :
  @semax_body [] (hc3_G_init_img) CSmr FH.f_resp_img (resp_img_spec).
Proof.
  start_function.
  unfold resp_rep. Intros.
  rewrite hc3b_msg_resp_eq by auto.
  assert_PROP (@field_compatible HCS (tarray tuchar 92) [] i) by (unfold hout; entailer!).
  sep_apply (hc3b_msg_resp_out shi i M); auto.
  repeat flatten_sepcon_in_SEP.
  pose proof H as (L1&L2&L3&L4).
  assert (Pi: isptr i) by (destruct H0; auto).
  assert_PROP (@field_compatible CSmr t_resp [] m) as FCm
    by (entailer!; match goal with H: @field_compatible _ t_resp (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  assert (Pm: isptr m) by (destruct FCm; auto).
  forward.
  forward_call (shi, i, rm_type M).
  forward.
  forward_call (shi, offset_val 4 i, rm_sender M).
  forward.
  forward_call (shi, offset_val 8 i, rm_receiver M).
  forward_call (shi, offset_val 12 i, shm, @field_address CSmr t_resp (DOT FH._unencrypted_ephemeral) m, rm_eph M).
  try (entailer!; simpl; rewrite L1; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  forward_call (shi, offset_val 44 i, shm, @field_address CSmr t_resp (DOT FH._encrypted_nothing) m, rm_encn M).
  try (entailer!; simpl; rewrite L2; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  forward_call (shi, offset_val 60 i, shm, @field_address CSmr t_resp (DOT FH._macs DOT FH._mac1) m, rm_mac1 M).
  try (entailer!; simpl; rewrite L3; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  forward_call (shi, offset_val 76 i, shm, @field_address CSmr t_resp (DOT FH._macs DOT FH._mac2) m, rm_mac2 M).
  try (entailer!; simpl; rewrite L4; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  sep_apply (hc3b_msg_resp_in shi i M); auto.
  unfold resp_rep. rewrite hc3b_msg_resp_eq by auto.
  entailer!.
Qed.

Lemma hc3_body_cookie_img :
  @semax_body [] (hc3_G_init_img) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_cookie_img (cookie_img_spec).
Proof.
  start_function.
  unfold cmsg_rep. Intros.
  rewrite hc3b_msg_cookie_eq by auto.
  assert_PROP (@field_compatible HCS (tarray tuchar 64) [] i) by (unfold hout; entailer!).
  sep_apply (hc3b_msg_cookie_out shi i M); auto.
  repeat flatten_sepcon_in_SEP.
  pose proof H as (L1&L2).
  assert (Pi: isptr i) by (destruct H0; auto).
  assert_PROP (@field_compatible hc3b_msg_KCS t_cmsg [] m) as FCm
    by (entailer!; match goal with H: @field_compatible _ t_cmsg (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  assert (Pm: isptr m) by (destruct FCm; auto).
  forward.
  forward_call (shi, i, cm_type M).
  forward.
  forward_call (shi, offset_val 4 i, cm_receiver M).
  forward_call (shi, offset_val 8 i, shm, @field_address hc3b_msg_KCS t_cmsg (DOT FK._nonce) m, cm_nonce M).
  try (entailer!; simpl; rewrite L1; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  forward_call (shi, offset_val 32 i, shm, @field_address hc3b_msg_KCS t_cmsg (DOT FK._encrypted_cookie) m, cm_enc M).
  try (entailer!; simpl; rewrite L2; rewrite ?field_address_offset by auto with field_compatible; rewrite ?offset_offset_val; reflexivity).
  sep_apply (hc3b_msg_cookie_in shi i M); auto.
  unfold cmsg_rep. rewrite hc3b_msg_cookie_eq by auto.
  entailer!.
Qed.

Lemma hc3_body_fill_init :
  @semax_body [] (hc3_G_fill_init) CSmi FH.f_fill_init (fill_init_spec).
Proof.
  start_function.
  rewrite hc3b_msg_init_eq_.
  assert_PROP (field_compatible t_init [] m) as FCm
    by (entailer!; match goal with H: field_compatible t_init (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  assert (Pm: isptr m) by (destruct FCm; auto).
  forward_call. Intros n1.
  forward.
  forward_call. Intros n2.
  forward.
  forward_call (field_address t_init (DOT FH._unencrypted_ephemeral) m, 32, shm).
  Intros b1.
  forward_call (field_address t_init (DOT FH._encrypted_static) m, 48, shm).
  Intros b2.
  forward_call (field_address t_init (DOT FH._encrypted_timestamp) m, 28, shm).
  Intros b3.
  forward_call (field_address t_init (DOT FH._macs DOT FH._mac1) m, 16, shm).
  Intros b4.
  forward_call (field_address t_init (DOT FH._macs DOT FH._mac2) m, 16, shm).
  Intros b5.
  assert (OK: im_ok (mkIM (Int.repr n1) (Int.repr n2) (map Byte.repr b1) (map Byte.repr b2) (map Byte.repr b3)
    (map Byte.repr b4) (map Byte.repr b5))) by (unfold im_ok; simpl; rewrite !Zlength_map; auto).
  rewrite !hc3b_msg_nd by auto.
  Exists (mkIM (Int.repr n1) (Int.repr n2) (map Byte.repr b1) (map Byte.repr b2) (map Byte.repr b3)
    (map Byte.repr b4) (map Byte.repr b5)).
  unfold init_rep. rewrite hc3b_msg_init_eq by auto.
  entailer!.
Qed.

Lemma hc3_body_fill_resp :
  @semax_body [] (hc3_G_fill_resp) CSmr FH.f_fill_resp (fill_resp_spec).
Proof.
  start_function.
  rewrite hc3b_msg_resp_eq_.
  assert_PROP (@field_compatible CSmr t_resp [] m) as FCm
    by (entailer!; match goal with H: @field_compatible _ t_resp (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  assert (Pm: isptr m) by (destruct FCm; auto).
  forward_call. Intros n1.
  forward.
  forward_call. Intros n2.
  forward.
  forward_call. Intros n3.
  forward.
  forward_call (@field_address CSmr t_resp (DOT FH._unencrypted_ephemeral) m, 32, shm).
  Intros b1.
  forward_call (@field_address CSmr t_resp (DOT FH._encrypted_nothing) m, 16, shm).
  Intros b2.
  forward_call (@field_address CSmr t_resp (DOT FH._macs DOT FH._mac1) m, 16, shm).
  Intros b3.
  forward_call (@field_address CSmr t_resp (DOT FH._macs DOT FH._mac2) m, 16, shm).
  Intros b4.
  assert (OK: rm_ok (mkRM (Int.repr n1) (Int.repr n2) (Int.repr n3) (map Byte.repr b1) (map Byte.repr b2)
    (map Byte.repr b3) (map Byte.repr b4))) by (unfold rm_ok; simpl; rewrite !Zlength_map; auto).
  rewrite !hc3b_msg_nd by auto.
  Exists (mkRM (Int.repr n1) (Int.repr n2) (Int.repr n3) (map Byte.repr b1) (map Byte.repr b2)
    (map Byte.repr b3) (map Byte.repr b4)).
  unfold resp_rep. rewrite hc3b_msg_resp_eq by auto.
  entailer!.
Qed.

Lemma hc3_body_fill_cookie_msg :
  @semax_body [] (hc3_G_fill_cookie_msg) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_fill_cookie_msg (fill_cookie_msg_spec).
Proof.
  start_function.
  rewrite hc3b_msg_cookie_eq_.
  assert_PROP (@field_compatible hc3b_msg_KCS t_cmsg [] m) as FCm
    by (entailer!; match goal with H: @field_compatible _ t_cmsg (DOT _ DOT _) m |- _ =>
          destruct H as (?&?&?&?&?); repeat split; auto end).
  assert (Pm: isptr m) by (destruct FCm; auto).
  forward_call. Intros n1.
  forward.
  forward_call. Intros n2.
  forward.
  forward_call (@field_address hc3b_msg_KCS t_cmsg (DOT FK._nonce) m, 24, shm).
  Intros b1.
  forward_call (@field_address hc3b_msg_KCS t_cmsg (DOT FK._encrypted_cookie) m, 32, shm).
  Intros b2.
  assert (OK: cm_ok (mkCM (Int.repr n1) (Int.repr n2) (map Byte.repr b1) (map Byte.repr b2)))
    by (unfold cm_ok; simpl; rewrite !Zlength_map; auto).
  rewrite !hc3b_msg_nd by auto.
  Exists (mkCM (Int.repr n1) (Int.repr n2) (map Byte.repr b1) (map Byte.repr b2)).
  unfold cmsg_rep. rewrite hc3b_msg_cookie_eq by auto.
  entailer!.
Qed.

(* the group *)
Theorem hc3_bodies_msg :
  (@semax_body [] (hc3_G_init_img) CSmi FH.f_init_img (init_img_spec)) /\
  (@semax_body [] (hc3_G_init_img) CSmr FH.f_resp_img (resp_img_spec)) /\
  (@semax_body [] (hc3_G_init_img) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_cookie_img (cookie_img_spec)) /\
  (@semax_body [] (hc3_G_fill_init) CSmi FH.f_fill_init (fill_init_spec)) /\
  (@semax_body [] (hc3_G_fill_resp) CSmr FH.f_fill_resp (fill_resp_spec)) /\
  (@semax_body [] (hc3_G_fill_cookie_msg) WgNoise.contracts.x_cookie_reply.Harness.CS FK.f_fill_cookie_msg (fill_cookie_msg_spec)).
Proof.
  exact (conj hc3_body_init_img (conj hc3_body_resp_img (conj hc3_body_cookie_img
    (conj hc3_body_fill_init (conj hc3_body_fill_resp hc3_body_fill_cookie_msg))))).
Qed.

End Bodies.
