(* law handshake_receive, phase B8, branch E: the pure lemma: the world after the packet in branch E.
   Statement: hrx5_B8_E_defs.v. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_E_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* helpers (ports of B6's hrx5_B6_pure.v under the prefix hrx5_b8ep_)       *)
(* ---------------------------------------------------------------------- *)
Section Helpers.
Local Open Scope Z_scope.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_b8ep_fwd_len msg : hrx5_fwd msg = true ->
  (Int.eq (hrx5_tw msg) Int.one = true /\ Zlength msg = 148) \/
  (Int.eq (hrx5_tw msg) (Int.repr 2) = true /\ Zlength msg = 92) \/
  (Int.eq (hrx5_tw msg) (Int.repr 3) = true /\ Zlength msg = 64).
Proof.
  unfold hrx5_fwd. intros H. apply andb_prop in H. destruct H as [_ H].
  apply orb_prop in H. destruct H as [H|H]; [apply orb_prop in H; destruct H as [H|H]|];
    apply andb_prop in H; destruct H as [H1 H2]; apply Z.eqb_eq in H2; auto.
Qed.

Lemma hrx5_b8ep_rlen M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (A & B & C & D). unfold resp_bytes. rewrite !Zlength_app, A, B, C, D. reflexivity.
Qed.

Lemma hrx5_b8ep_clen M : cm_ok M -> Zlength (cookie_msg_bytes M) = 64.
Proof.
  intros (A & B). unfold cookie_msg_bytes. rewrite !Zlength_app, A, B. reflexivity.
Qed.

Lemma hrx5_b8ep_ilen M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (A & B & C & D & E). unfold init_bytes. rewrite !Zlength_app, A, B, C, D, E. reflexivity.
Qed.

Lemma hrx5_b8ep_obj (o: hrx5_obj) :
  obj_ok o -> hrx5_fwd (obj_bytes o) = true ->
  ((obj_kind o = 1 \/ obj_kind o = 2) -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = false) /\
  (obj_kind o <> 1 -> obj_kind o <> 2 -> Int.eq (hrx5_tw (obj_bytes o)) (Int.repr 3) = true).
Proof.
  intros Ho Hf. pose proof (hrx5_b8ep_fwd_len _ Hf) as HL.
  destruct o as [b|M|M|M]; cbn [obj_ok obj_bytes obj_kind] in *.
  - destruct Ho as (A & B & C & _). destruct HL as [[_ X]|[[_ X]|[_ X]]]; lia.
  - pose proof (hrx5_b8ep_ilen _ Ho) as L. rewrite L in HL.
    destruct HL as [[X _]|[[_ X]|[_ X]]]; try lia. apply Int.same_if_eq in X. rewrite X.
    split; [reflexivity | intros H1; exfalso; lia].
  - pose proof (hrx5_b8ep_rlen _ Ho) as L. rewrite L in HL.
    destruct HL as [[_ X]|[[X _]|[_ X]]]; try lia. apply Int.same_if_eq in X. rewrite X.
    split; [reflexivity | intros H1 H2; exfalso; lia].
  - pose proof (hrx5_b8ep_clen _ Ho) as L. rewrite L in HL.
    destruct HL as [[_ X]|[[_ X]|[X _]]]; try lia. apply Int.same_if_eq in X. rewrite X.
    split; [intros [H1|H1]; discriminate | intros; reflexivity].
Qed.

Lemma hrx5_b8ep_vm_snd CC s msg ul now rl r :
  snd (validate_model CC s msg ul now rl r) =
  if validate_rotates CC msg ul now then checker_rotate CC now r else CC.
Proof.
  unfold validate_model, validate_rotates.
  destruct (bytes_eqb _ _); cbn [negb andb]; [| reflexivity].
  destruct ul; cbn [negb andb]; [| reflexivity].
  destruct (checker_rotates CC now) eqn:E.
  - destruct (negb _); [reflexivity | destruct rl; reflexivity].
  - assert (E2: checker_rotate CC now r = CC) by (unfold checker_rotate, checker_rotates in *; rewrite E; reflexivity).
    rewrite E2. destruct (negb _); [reflexivity | destruct rl; reflexivity].
Qed.

(* the bytes of a little-endian u32 *)
Lemma hrx5_b8ep_le32 x : le32_val (le32 x) = x.
Proof.
  unfold le32_val, le32. cbn [map]. unfold Znth. cbn - [Z.pow Z.div Byte.repr].
  rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  pose proof (Int.unsigned_range x) as Hx. change Int.modulus with (2 ^ 32) in Hx.
  set (u := Int.unsigned x) in *.
  replace (u / 2 ^ 0) with u by (symmetry; apply Z.div_1_r).
  replace (2 ^ 16) with (256 * 256) by reflexivity.
  replace (2 ^ 24) with (256 * 256 * 256) by reflexivity.
  replace (2 ^ 8) with 256 by reflexivity.
  rewrite <- !Z.div_div by lia.
  set (a := u / 256). set (b := a / 256). set (c := b / 256).
  assert (Ha: u = 256 * a + u mod 256) by (apply Z.div_mod; lia).
  assert (Hb: a = 256 * b + a mod 256) by (apply Z.div_mod; lia).
  assert (Hc: b = 256 * c + b mod 256) by (apply Z.div_mod; lia).
  pose proof (Z.mod_pos_bound u 256 ltac:(lia)). pose proof (Z.mod_pos_bound a 256 ltac:(lia)).
  pose proof (Z.mod_pos_bound b 256 ltac:(lia)).
  assert (Hc0: 0 <= c < 256).
  { subst c b a. rewrite !Z.div_div by lia. split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]. }
  rewrite (Z.mod_small c 256) by lia.
  rewrite <- (Int.repr_unsigned x). fold u. f_equal. lia.
Qed.

Lemma hrx5_b8ep_le32_len x : Zlength (le32 x) = 4.
Proof. reflexivity. Qed.

Lemma hrx5_b8ep_im_of M : im_ok M -> im_of (init_bytes M) = M.
Proof.
  destruct M as [t0 t1 e es et m1 m2]. intros (A & B & C & D & E); simpl in A, B, C, D, E.
  unfold im_of, init_bytes; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  pose proof (hrx5_b8ep_le32_len t0) as L1. pose proof (hrx5_b8ep_le32_len t1) as L2.
  replace (sublist 0 4 _) with (le32 t0) by list_solve.
  replace (sublist 4 8 _) with (le32 t1) by list_solve.
  rewrite !hrx5_b8ep_le32. f_equal; list_solve.
Qed.

Lemma hrx5_b8ep_rm_of M : rm_ok M -> rm_of (resp_bytes M) = M.
Proof.
  destruct M as [t0 t1 t2 e en m1 m2]. intros (A & B & C & D); simpl in A, B, C, D.
  unfold rm_of, resp_bytes; cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
  pose proof (hrx5_b8ep_le32_len t0) as L1. pose proof (hrx5_b8ep_le32_len t1) as L2.
  pose proof (hrx5_b8ep_le32_len t2) as L3.
  replace (sublist 0 4 _) with (le32 t0) by list_solve.
  replace (sublist 4 8 _) with (le32 t1) by list_solve.
  replace (sublist 8 12 _) with (le32 t2) by list_solve.
  rewrite !hrx5_b8ep_le32. f_equal; list_solve.
Qed.

Lemma hrx5_b8ep_cm_of M : cm_ok M -> cm_of (cookie_msg_bytes M) = M.
Proof.
  destruct M as [t0 t1 n e]. intros (A & B); simpl in A, B.
  unfold cm_of, cookie_msg_bytes; cbn [cm_type cm_receiver cm_nonce cm_enc].
  pose proof (hrx5_b8ep_le32_len t0) as L1. pose proof (hrx5_b8ep_le32_len t1) as L2.
  replace (sublist 0 4 _) with (le32 t0) by list_solve.
  replace (sublist 4 8 _) with (le32 t1) by list_solve.
  rewrite !hrx5_b8ep_le32. f_equal; list_solve.
Qed.

Lemma hrx5_b8ep_w4_init M : im_ok M -> hrx5_w4 (init_bytes M) = im_sender M.
Proof. intros H. rewrite <- (hrx5_b8ep_im_of M H) at 2. reflexivity. Qed.

Lemma hrx5_b8ep_w4_resp M : rm_ok M -> hrx5_w4 (resp_bytes M) = rm_sender M.
Proof. intros H. rewrite <- (hrx5_b8ep_rm_of M H) at 2. reflexivity. Qed.

(* the shim: draws keep the counters *)
Lemma hrx5_b8ep_eqb_draw S w S' r : shim_eqb S w (shim_draw S' r) w = shim_eqb S w S' w.
Proof. reflexivity. Qed.

Lemma hrx5_b8ep_eqb_refl S w : shim_eqb S w S w = true.
Proof.
  unfold shim_eqb, warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity.
Qed.

(* the node of a peer of the list *)
Lemma hrx5_b8ep_nfind NS a : In a (map hn_p NS) -> In (hrx5_nfind NS a) (map hn_addr NS).
Proof.
  induction NS as [|N NS IH]; cbn [map In hrx5_nfind]; [tauto |].
  intros H. destruct (eq_dec (hn_p N) a); [left; reflexivity |].
  right. apply IH. destruct H; [contradiction | assumption].
Qed.

Lemma hrx5_b8ep_sfind_in (l: list (val * share * peer)) a sh v :
  sfind l a = Some (sh, v) -> In a (map peer_addr4 l).
Proof.
  induction l as [|[[x sx] y] l IH]; cbn [sfind map In]; [discriminate |].
  destruct (eq_dec x a) as [<-|n]; [intros _; left; reflexivity |].
  intros H; right; apply IH; exact H.
Qed.

Lemma hrx5_b8ep_ck_tgt T PS M a P pt :
  hrx5ck_tgt xaead_dec T PS M = Some (a, P, pt) -> In a (map peer_addr4 PS).
Proof.
  unfold hrx5ck_tgt.
  destruct (t_find_index T (t_L T) (cm_receiver M)) as [[b E]|]; [| discriminate].
  destruct (Int.eq _ Int.zero); [discriminate |].
  destruct (sfind PS (e_peer E)) as [[sh P0]|] eqn:HS; [| discriminate].
  destruct (ck_sent _); [| discriminate].
  destruct (xaead_dec _ _ _ _); [| discriminate].
  intros H; inversion H; subst. eapply hrx5_b8ep_sfind_in; exact HS.
Qed.
End Helpers.

Section Hs.
Local Open Scope Z_scope.

Lemma hrx5_b8ep_tw_init M : im_ok M -> hrx5_fwd (init_bytes M) = true ->
  Int.eq (hrx5_tw (init_bytes M)) Int.one = true.
Proof.
  intros Ho Hf. pose proof (hrx5_b8ep_ilen _ Ho) as L.
  destruct (hrx5_b8ep_fwd_len _ Hf) as [[X _]|[[_ X]|[_ X]]]; rewrite ?L in X; try lia; exact X.
Qed.

Lemma hrx5_b8ep_tw_resp M : rm_ok M -> hrx5_fwd (resp_bytes M) = true ->
  Int.eq (hrx5_tw (resp_bytes M)) Int.one = false.
Proof.
  intros Ho Hf. pose proof (hrx5_b8ep_rlen _ Ho) as L.
  destruct (hrx5_b8ep_fwd_len _ Hf) as [[_ X]|[[X _]|[_ X]]]; rewrite ?L in X; try lia.
  apply Int.same_if_eq in X. rewrite X. reflexivity.
Qed.

(* the device: D at the locals with some 32-byte secret born before 2^62 *)
Definition hrx5_b8ep_dgood x25519 (R: hrx5_run) (L: hrx5_loc) (D': device) : Prop :=
  exists sec1 birth1, D' = hrx5_DL x25519 R L sec1 birth1 /\ Zlength sec1 = 32 /\
    0 <= Int64.unsigned birth1 < 2 ^ 62.

Lemma hrx5_b8ep_dgood_rot x25519 R L D' now r :
  hrx5_b8ep_dgood x25519 R L D' -> Zlength r = 32 -> 0 <= Int64.unsigned now < 2 ^ 62 ->
  hrx5_b8ep_dgood x25519 R L (dev_set_cc D' (checker_rotate (d_cc D') now r)).
Proof.
  intros (s1 & b1 & -> & H1 & H2) Hr Hn. unfold checker_rotate.
  destruct (birthdate_expired _ _ _).
  - exists r, now. split; [reflexivity | auto].
  - exists s1, b1. split; [reflexivity | auto].
Qed.

Lemma hrx5_b8ep_dgood_vm x25519 R L D' s msg ul now rl r :
  hrx5_b8ep_dgood x25519 R L D' -> Zlength r = 32 -> 0 <= Int64.unsigned now < 2 ^ 62 ->
  hrx5_b8ep_dgood x25519 R L (dev_set_cc D' (snd (validate_model (d_cc D') s msg ul now rl r))).
Proof.
  intros HD Hr Hn. rewrite hrx5_b8ep_vm_snd.
  destruct (validate_rotates _ _ _ _).
  - apply hrx5_b8ep_dgood_rot; auto.
  - destruct HD as (s1 & b1 & -> & H1 & H2). exists s1, b1. split; [reflexivity | auto].
Qed.

(* a forwarded initiation / response (type word not 3), the consume function rejecting on path 1 *)
Lemma hrx5_b8ep_hs x25519 aead_dec xaead_enc xaead_dec R L sec birth T PS S w kc lul q sp s msg d :
  hrx5_base_ok R sec birth S -> Zlength (rd_r d) = 32 -> Zlength (rd_r2 d) = 32 ->
  hrx5_fwd msg = true -> Int.eq (hrx5_tw msg) (Int.repr 3) = false ->
  (hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q s msg d = 1 ->
   forall D' S', d_id D' = d_id (hrx5_DL x25519 R L sec birth) -> s_boot S' = s_boot S ->
     if Int.eq (hrx5_tw msg) Int.one then cin_res x25519 aead_dec D' PS (im_of msg) S' = None
     else cre_res x25519 aead_dec D' T PS (rm_of msg) = None) ->
  exists sec1 birth1 S1 lul1,
    rx_model x25519 aead_dec xaead_enc xaead_dec (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul)
      q sp s msg d =
      mkRW (hrx5_DL x25519 R L sec1 birth1) T PS [] S1 w kc lul1
        (if Z.eq_dec (hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q s msg d) 2
         then rx_send_cookie rx0 (hrx5_w4 msg) else rx0) /\
    hrx5_base_ok R sec1 birth1 S1 /\ s_boot S1 = s_boot S /\ shim_eqb S w S1 w = true /\
    0 <= hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q s msg d <= 2.
Proof.
  intros Hb Hr Hr2 Hf Ht Hc.
  assert (Hn: 0 <= Int64.unsigned (s_boot S) < 2 ^ 62) by apply Hb.
  destruct Hb as (Hrun & Hsec & Hbirth & _).
  unfold rx_model, hrx5_path in *. rewrite Hf in *. unfold rx_packet. cbv zeta in Hc |- *. rewrite Ht in *.
  unfold hrx5_W0 in *. cbn [rw_D rw_S rw_lul rw_T rw_PS rw_KS rw_w rw_kc rw_rx] in *.
  set (D := hrx5_DL x25519 R L sec birth) in *.
  set (now := s_boot S) in *.
  set (ul := fst (load_model q lul now)) in *.
  set (vm := validate_model (d_cc D) s msg ul now (s_rlallow S) (rd_r d)) in *.
  set (S1 := if validate_rotates (d_cc D) msg ul now then shim_draw S (rd_r d) else S).
  assert (HS1a: s_boot S1 = now) by (subst S1; destruct (validate_rotates _ _ _ _); reflexivity).
  assert (HS1b: shim_eqb S w S1 w = true).
  { subst S1. destruct (validate_rotates _ _ _ _); rewrite ?hrx5_b8ep_eqb_draw; apply hrx5_b8ep_eqb_refl. }
  assert (HD1: hrx5_b8ep_dgood x25519 R L (dev_set_cc D (snd vm))).
  { apply hrx5_b8ep_dgood_vm; auto. exists sec, birth. auto. }
  assert (Hbase: forall sec1 birth1, Zlength sec1 = 32 -> 0 <= Int64.unsigned birth1 < 2 ^ 62 ->
    forall S2, s_boot S2 = now -> hrx5_base_ok R sec1 birth1 S2).
  { intros sec1 birth1 H1 H2 S2 H3. split; [exact Hrun | split; [exact H1 | split; [exact H2 | rewrite H3; exact Hn]]]. }
  destruct (rx_consumes ul (fst vm)) eqn:Ec.
  - specialize (Hc eq_refl (dev_set_cc D (snd vm)) S1 eq_refl HS1a).
    destruct HD1 as (sec1 & birth1 & HD1 & Hs1 & Hb1).
    exists sec1, birth1, S1, (snd (load_model q lul now)).
    destruct (Z.eq_dec 1 2) as [C|_]; [discriminate |].
    destruct (Int.eq (hrx5_tw msg) Int.one); rewrite Hc, HD1.
    all: split; [reflexivity |]; split; [apply Hbase; auto |]; split; [exact HS1a |]; split; [exact HS1b | lia].
  - destruct (rx_needs_cookie ul (fst vm)) eqn:En.
    + destruct (Z.eq_dec 2 2) as [_|C]; [| congruence].
      unfold mc_res, message_create_model. cbn [snd]. rewrite HS1a.
      change (dev_set_cc D (checker_rotate (snd vm) now (rd_r2 d))) with
        (dev_set_cc (dev_set_cc D (snd vm)) (checker_rotate (d_cc (dev_set_cc D (snd vm))) now (rd_r2 d))).
      pose proof (hrx5_b8ep_dgood_rot _ _ _ _ now (rd_r2 d) HD1 Hr2 Hn) as HD2.
      destruct HD2 as (sec1 & birth1 & HD2 & Hs1 & Hb1). rewrite HD2.
      set (S2 := if checker_rotates (snd vm) now then shim_draw (shim_draw S1 (rd_nonce d)) (rd_r2 d)
                 else shim_draw S1 (rd_nonce d)).
      assert (HS2a: s_boot S2 = now) by (subst S2; destruct (checker_rotates _ _); exact HS1a).
      assert (HS2b: shim_eqb S w S2 w = true)
        by (subst S2; destruct (checker_rotates _ _); rewrite !hrx5_b8ep_eqb_draw; exact HS1b).
      exists sec1, birth1, S2, (snd (load_model q lul now)).
      split; [reflexivity |]; split; [apply Hbase; auto |]; split; [exact HS2a |]; split; [exact HS2b | lia].
    + destruct (Z.eq_dec 0 2) as [C|_]; [discriminate |].
      destruct HD1 as (sec1 & birth1 & HD1 & Hs1 & Hb1). rewrite HD1.
      exists sec1, birth1, S1, (snd (load_model q lul now)).
      split; [reflexivity |]; split; [apply Hbase; auto |]; split; [exact HS1a |]; split; [exact HS1b | lia].
Qed.

End Hs.

Lemma hrx5_B8E_P_ok : hrx5_B8E_pure_stmt.
Proof.
  unfold hrx5_B8E_pure_stmt.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE kc lul q proto ip4 ip6
    port o dp tg ai ar d Hhyps Hbase Hinv Ho Hacc Hd Hnn.
  cbv zeta. unfold hrx5_B8_path, hrx5_B8_isE, hrx5_B8_isI, hrx5_B8_isR, hrx5_B8_isC.
  intros (HnI & HnR & HnC).
  destruct Hd as (Hdr & Hdn & Hdr2 & _).
  destruct (hrx5_fwd (obj_bytes o)) eqn:Hf.
  2: { assert (Hp0: hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q
                      (hrx5_skb dp o proto ip4 ip6 port) (obj_bytes o) d = 0)
         by (unfold hrx5_path; rewrite Hf; reflexivity).
       rewrite Hp0. unfold rx_model. rewrite Hf.
       exists sec, birth, S, lul. split; [reflexivity |]. split; [exact Hbase |]. split; [reflexivity |].
       split; [apply hrx5_b8ep_eqb_refl |]. split; [lia | intros; lia]. }
  pose proof (hrx5_b8ep_obj o Ho Hf) as [Hk12 Hk3].
  destruct Hinv as (Hpok & Hwf & Hnd & Hch & Hnp & Hnk & Hpool).
  unfold hrx5_acc_ok in Hacc. cbv zeta in Hacc. rewrite Hf in Hacc.
  destruct o as [b|M|M|M]; cbn [obj_bytes obj_kind obj_ok] in *.
  - (* any bytes: never forwarded *)
    exfalso. destruct Ho as (A & B & C & _).
    destruct (hrx5_b8ep_fwd_len _ Hf) as [[_ X]|[[_ X]|[_ X]]]; lia.
  - (* an initiation *)
    specialize (Hk12 (or_introl eq_refl)).
    destruct (hrx5_b8ep_hs x25519 aead_dec xaead_enc xaead_dec R L sec birth T PS S w kc lul q (l_skb L)
      (hrx5_skb dp (OInit M) proto ip4 ip6 port) (init_bytes M) d Hbase Hdr Hdr2 Hf Hk12)
      as (sec1 & birth1 & S1 & lul1 & E & Hb1 & Hs1 & He1 & Hp).
    + intros Hp1 D' S' HD' HS'.
      rewrite (hrx5_b8ep_tw_init M Ho Hf), (hrx5_b8ep_im_of M Ho).
      destruct Hacc as [_ Hacc].
      destruct (hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M (s_boot S)) as [[[[[a P] t] ck] h]|] eqn:Htg.
      { exfalso. destruct Hacc as [Hai _]. apply HnI. auto. }
      rewrite (hrx5ci_agree x25519 aead_dec (rr_rawd R) D' PS M S').
      * unfold hrx5ci_res. rewrite HS'. change (mident_of x25519 (rr_rawd R)) with (hrx5_ID x25519 R).
        rewrite Htg. reflexivity.
      * rewrite HD'. reflexivity.
      * rewrite HD'. eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] HP.
        destruct HP as (_ & _ & _ & _ & Hss & Hrefs & _). split; [exact Hss |].
        intros E0. rewrite E0, Int.unsigned_zero in Hrefs. lia.
    + exists sec1, birth1, S1, lul1. rewrite E. unfold hrx5_B8E_W, hrx5_B8E_log. cbn [hrx5_B8E_sidx].
      rewrite (hrx5_b8ep_w4_init M Ho).
      split; [reflexivity |]. split; [exact Hb1 |]. split; [exact Hs1 |]. split; [exact He1 |].
      split; [exact Hp | intros _; left; reflexivity].
  - (* a response *)
    specialize (Hk12 (or_intror eq_refl)).
    destruct (hrx5_b8ep_hs x25519 aead_dec xaead_enc xaead_dec R L sec birth T PS S w kc lul q (l_skb L)
      (hrx5_skb dp (OResp M) proto ip4 ip6 port) (resp_bytes M) d Hbase Hdr Hdr2 Hf Hk12)
      as (sec1 & birth1 & S1 & lul1 & E & Hb1 & Hs1 & He1 & Hp).
    + intros Hp1 D' S' HD' HS'.
      rewrite (hrx5_b8ep_tw_resp M Ho Hf), (hrx5_b8ep_rm_of M Ho).
      destruct Hacc as [_ Hacc].
      destruct (hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M) as [[[[a P] ck] h]|] eqn:Htg.
      { exfalso. destruct Hacc as [Har _]. apply HnR. auto. }
      unfold cre_res.
      replace (d_id D') with (d_id (hrx5cr_DA x25519 (mkRunCR5 (rr_rawd R) [] [] Int64.zero) nullval nullval nullval))
        by (rewrite HD'; reflexivity).
      rewrite (hrx5cr_agree x25519 aead_dec _ nullval nullval nullval T (map ke_addr KE) PS M).
      * change (hrx5cr_IA x25519 (mkRunCR5 (rr_rawd R) [] [] Int64.zero)) with (hrx5_ID x25519 R).
        rewrite Htg. reflexivity.
      * unfold peers_refs_ok. eapply Forall_impl; [| exact Hpok]. intros [[a sh] P] HP.
        destruct HP as (_ & _ & _ & _ & _ & Hrefs & _). exact Hrefs.
      * exact Hpool.
    + exists sec1, birth1, S1, lul1. rewrite E. unfold hrx5_B8E_W, hrx5_B8E_log. cbn [hrx5_B8E_sidx].
      rewrite (hrx5_b8ep_w4_resp M Ho).
      split; [reflexivity |]. split; [exact Hb1 |]. split; [exact Hs1 |]. split; [exact He1 |].
      split; [exact Hp | intros _; right; reflexivity].
  - (* a cookie reply *)
    specialize (Hk3 ltac:(discriminate) ltac:(discriminate)).
    assert (Hp1: hrx5_path (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) q
                   (hrx5_skb dp (OCookie M) proto ip4 ip6 port) (cookie_msg_bytes M) d = 1)
      by (unfold hrx5_path; rewrite Hf, Hk3; reflexivity).
    rewrite Hp1 in *.
    destruct Hacc as (_ & _ & Htg).
    assert (Htg0: tg = nullval).
    { destruct (eq_dec tg nullval) as [X|X]; [exact X |]. exfalso. apply HnC. auto. }
    destruct (hrx5ck_tgt xaead_dec T PS M) as [[[a P] pt]|] eqn:Hck.
    + exfalso. apply Hnn. rewrite <- Htg0, Htg. apply hrx5_b8ep_nfind.
      unfold hnodes_peers4 in Hnp. rewrite Hnp. eapply hrx5_b8ep_ck_tgt; exact Hck.
    + exists sec, birth, S, lul.
      unfold rx_model. rewrite Hf. unfold rx_packet. cbv zeta. rewrite Hk3.
      unfold hrx5_W0. cbn [rw_D rw_S rw_lul rw_T rw_PS rw_KS rw_w rw_kc rw_rx].
      unfold mcons_res. rewrite (hrx5_b8ep_cm_of M Ho), hrx5ck_agree, Hck. cbn [peers_after].
      split; [reflexivity |]. split; [exact Hbase |]. split; [reflexivity |].
      split; [apply hrx5_b8ep_eqb_refl |]. split; [lia | intros; discriminate].
Qed.
