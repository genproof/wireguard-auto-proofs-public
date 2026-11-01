(* law handshake_receive, phase B8 branch I: the PURE analysis of branch I:
   the message object, the harness's model block and the receive model's world after the accepted initiation. *)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_I_defs.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the initiation's image                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_le32 v : le32_val (le32 v) = v.
Proof.
  unfold le32_val, le32. cbn [map].
  assert (Z0: forall (x0 x1 x2 x3: byte), Znth 0 [x0; x1; x2; x3] = x0) by reflexivity.
  assert (Z1: forall (x0 x1 x2 x3: byte), Znth 1 [x0; x1; x2; x3] = x1) by reflexivity.
  assert (Z2: forall (x0 x1 x2 x3: byte), Znth 2 [x0; x1; x2; x3] = x2) by reflexivity.
  assert (Z3: forall (x0 x1 x2 x3: byte), Znth 3 [x0; x1; x2; x3] = x3) by reflexivity.
  rewrite Z0, Z1, Z2, Z3. clear Z0 Z1 Z2 Z3.
  pose proof (Int.unsigned_range v) as Hv. set (u := Int.unsigned v) in *.
  rewrite !Byte.unsigned_repr_eq. change Byte.modulus with 256.
  change (2 ^ (8 * 0)) with 1. change (2 ^ (8 * 1)) with 256. change (2 ^ (8 * 2)) with 65536.
  change (2 ^ (8 * 3)) with 16777216. change (2 ^ 8) with 256. change (2 ^ 16) with 65536.
  change (2 ^ 24) with 16777216. rewrite Z.div_1_r.
  rewrite <- (Int.repr_unsigned v). fold u. f_equal.
  change Int.modulus with 4294967296 in Hv.
  rewrite (Z.mod_small (u / 16777216) 256) by (split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (E1: u mod 256 + u / 256 mod 256 * 256 = u mod 65536).
  { pose proof (Z.mod_mul_r u 256 256 ltac:(lia) ltac:(lia)) as X. change (256 * 256) with 65536 in X. rewrite Z.quot_div_nonneg in X by lia.
    rewrite !Z.rem_mod_nonneg in X by (try apply Z.div_pos; lia). lia. }
  assert (E2: u mod 65536 + u / 65536 mod 256 * 65536 = u mod 16777216).
  { pose proof (Z.mod_mul_r u 65536 256 ltac:(lia) ltac:(lia)) as X. change (65536 * 256) with 16777216 in X. rewrite Z.quot_div_nonneg in X by lia.
    rewrite !Z.rem_mod_nonneg in X by (try apply Z.div_pos; lia). lia. }
  assert (E3: u mod 16777216 + u / 16777216 * 16777216 = u).
  { rewrite (Z.div_mod u 16777216) at 3 by lia. lia. }
  lia.
Qed.

Lemma hrx5_B8I_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). unfold init_bytes, le32. autorewrite with sublist.
  rewrite H1, H2, H3, H4, H5. reflexivity.
Qed.

Lemma hrx5_B8I_im_of M : im_ok M -> im_of (init_bytes M) = M.
Proof.
  intros (H1 & H2 & H3 & H4 & H5). destruct M as [ty snd eph encs enct m1 m2]; cbn [im_eph im_encs im_enct im_mac1 im_mac2] in *.
  unfold im_of, init_bytes; cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
  assert (L4: forall v, Zlength (le32 v) = 4) by reflexivity.
  pose proof (L4 ty) as Lty. pose proof (L4 snd) as Lsn.
  f_equal.
  - rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8I_le32.
  - rewrite sublist_app2 by (try rewrite L4; lia). rewrite L4. simpl Z.sub.
    rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8I_le32.
  - list_solve.
  - list_solve.
  - list_solve.
  - list_solve.
  - list_solve.
Qed.

Lemma hrx5_B8I_tw M : hrx5_tw (init_bytes M) = im_type M.
Proof.
  unfold hrx5_tw, init_bytes. rewrite sublist_app1 by (cbn; list_solve).
  rewrite sublist_same by reflexivity. apply hrx5_B8I_le32.
Qed.

Lemma hrx5_B8I_fwd_type M : im_ok M -> hrx5_fwd (init_bytes M) = true -> im_type M = Int.one.
Proof.
  intros Hok. unfold hrx5_fwd. rewrite hrx5_B8I_len, hrx5_B8I_tw by exact Hok.
  cbn [Z.leb Z.eqb Pos.eqb Z.compare Pos.compare Pos.compare_cont andb orb].
  rewrite !andb_false_r, !orb_false_r, andb_true_r.
  intros H. pose proof (Int.eq_spec (im_type M) Int.one) as E. rewrite H in E. exact E.
Qed.

(* ---------------------------------------------------------------------- *)
(* the checker after validate, the reference count                          *)
(* ---------------------------------------------------------------------- *)

Lemma hrx5_B8I_vm_cc CC s msg cc now rl r :
  snd (validate_model CC s msg cc now rl r) = CC \/
  snd (validate_model CC s msg cc now rl r) = checker_rotate CC now r.
Proof.
  unfold validate_model.
  destruct (negb (bytes_eqb _ _)); [left; reflexivity |].
  destruct (negb cc); [left; reflexivity |].
  destruct (negb (bytes_eqb _ _)); [right; reflexivity |].
  destruct (negb rl); right; reflexivity.
Qed.

Lemma hrx5_B8I_rot CC now r :
  checker_rotate CC now r = CC \/
  checker_rotate CC now r = mkChk r (cc_ekey CC) (cc_mkey CC) now (cc_dev CC).
Proof. unfold checker_rotate. destruct (birthdate_expired _ _ _); auto. Qed.

Lemma hrx5_B8I_rc r : 0 < Int.unsigned r < 2147483647 ->
  rc_sub1 (rc_add1 r) = r /\ rc_dec_warn (rc_add1 r) = (fun w => w) /\ Int.eq r Int.zero = false.
Proof.
  intros Hr. rewrite rc_add1_small by lia.
  assert (E: Int.unsigned (Int.add r Int.one) = Int.unsigned r + 1).
  { unfold Int.add. rewrite Int.unsigned_one, Int.unsigned_repr; [reflexivity | rep_lia]. }
  assert (N: rc_neg (Int.add r Int.one) = false).
  { unfold rc_neg. unfold Int.ltu. rewrite E, Int.unsigned_repr by rep_lia.
    destruct (zlt _ _); [reflexivity | lia]. }
  assert (E1: Int.eq (Int.add r Int.one) Int.one = false).
  { apply Int.eq_false. intros H. apply (f_equal Int.unsigned) in H. rewrite E, Int.unsigned_one in H. lia. }
  assert (E0: Int.eq (Int.add r Int.one) Int.zero = false).
  { apply Int.eq_false. intros H. apply (f_equal Int.unsigned) in H. rewrite E, Int.unsigned_zero in H. lia. }
  assert (Z0: Int.eq r Int.zero = false).
  { apply Int.eq_false. intros H. subst r. rewrite Int.unsigned_zero in Hr. lia. }
  unfold rc_sub1, rc_dec_warn. rewrite N, E1, E0. cbn [negb andb orb].
  split; [| split; [reflexivity | exact Z0]].
  rewrite Int.sub_add_opp, Int.add_assoc, Int.add_neg_zero, Int.add_zero. reflexivity.
Qed.

Lemma hrx5_B8I_warn_refl w : warn_eqb w w = true.
Proof. unfold warn_eqb. cbn [forallb]. rewrite !Int64.eq_true. reflexivity. Qed.

Lemma hrx5_B8I_shim_refl S w : shim_eqb S w S w = true.
Proof. unfold shim_eqb. rewrite !Int64.eq_true, hrx5_B8I_warn_refl. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the world after the accepted initiation                                 *)
(* ---------------------------------------------------------------------- *)

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hrx5_B8I_peer_pure R L NS PS KE T head nk :
  hrx5_inv x25519 R L NS PS KE T head nk ->
  Forall (hrx5ci_peer_pure x25519 (setup_identity x25519 (rr_rawd R))) PS.
Proof.
  intros (HF & _). eapply Forall_impl; [| exact HF].
  intros [[p sh] P] (_ & _ & _ & _ & Hss & Hrefs & _). split; [exact Hss |].
  intros H. rewrite H, Int.unsigned_zero in Hrefs. lia.
Qed.

Lemma hrx5_B8I_tgt_in IB PS M now a P t ck2 h2 :
  hrx5ci_tgt x25519 aead_dec IB PS M now = Some (a, P, t, ck2, h2) -> exists sh, In (a, sh, P) PS.
Proof.
  unfold hrx5ci_tgt. destruct (mi_ok IB); [| discriminate].
  destruct (m_consume_init1_model _ _ _ _ _) as [[[[s0 k] ck1] h1]|]; [| discriminate].
  destruct (pk_find PS s0) as [[a0 P0]|] eqn:Hf; [| discriminate].
  destruct (m_consume_init2_model _ _ _ _ _) as [[[t0 c0] h0]|]; [| discriminate].
  destruct (_ && _)%bool; [| discriminate]. intros H; inversion H; subst.
  exact (hrx5ci_model_pk_find _ _ _ _ Hf).
Qed.

Lemma hrx5_B8I_model L R sec birth S w NS PS T head nk KE kc lul q proto ip4 ip6 port dp M d a P t ck2 h2 :
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> im_ok M -> rxdraw_ok T d ->
  let W0 := hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul in
  let s := hrx5_skb dp (OInit M) proto ip4 ip6 port in
  hrx5_path W0 q s (init_bytes M) d = 1 ->
  hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M (s_boot S) = Some (a, P, t, ck2, h2) ->
  exists sec1 birth1 S1,
    rx_model x25519 aead_dec xaead_enc xaead_dec W0 q (l_skb L) s (init_bytes M) d =
      mkRW (hrx5_DL x25519 R L sec1 birth1) T (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) [] S1 w kc
        (snd (load_model q lul (s_boot S))) (hrx5_B8I_log a (l_skb L) (sk_len s)) /\
    hrx5_base_ok R sec1 birth1 S1 /\ s_boot S1 = s_boot S /\ shim_eqb S w S1 w = true /\
    hrx5_fwd (init_bytes M) = true.
Proof.
  intros Hb Hinv Hok Hd W0 s Hp Ht.
  unfold hrx5_path in Hp.
  destruct (hrx5_fwd (init_bytes M)) eqn:Hfwd; [| discriminate].
  pose proof (hrx5_B8I_fwd_type M Hok Hfwd) as Hty.
  rewrite hrx5_B8I_tw, Hty in Hp. rewrite (Int.eq_false Int.one (Int.repr 3)) in Hp by discriminate.
  unfold rx_model. rewrite Hfwd. unfold rx_packet.
  rewrite hrx5_B8I_tw, Hty. rewrite (Int.eq_false Int.one (Int.repr 3)) by discriminate. rewrite Int.eq_true.
  subst W0. cbn [rw_D rw_S rw_lul rw_T rw_PS rw_KS rw_w rw_kc rw_rx hrx5_W0] in Hp |- *.
  set (ul := fst (load_model q lul (s_boot S))) in *.
  set (vm := validate_model _ _ _ _ _ _ _) in *.
  destruct (rx_consumes ul (fst vm)) eqn:Hc; [| destruct (rx_needs_cookie ul (fst vm)); discriminate].
  rewrite hrx5_B8I_im_of by exact Hok.
  set (S1 := if validate_rotates _ _ _ _ then _ else _).
  assert (HS1: s_boot S1 = s_boot S /\ shim_eqb S w S1 w = true).
  { unfold S1. destruct (validate_rotates _ _ _ _); [| split; [reflexivity | apply hrx5_B8I_shim_refl]].
    split; [reflexivity |]. unfold shim_eqb, shim_draw. cbn [s_allocs s_fails s_frees s_released].
    rewrite !Int64.eq_true, hrx5_B8I_warn_refl. reflexivity. }
  clearbody S1. destruct HS1 as [HS1b HS1e].
  assert (Hv: snd vm = d_cc (hrx5_DL x25519 R L sec birth) \/
              snd vm = checker_rotate (d_cc (hrx5_DL x25519 R L sec birth)) (s_boot S) (rd_r d))
    by apply hrx5_B8I_vm_cc.
  clearbody vm. clear Hc Hp.
  rewrite (hrx5ci_agree x25519 aead_dec (rr_rawd R)).
  2: { reflexivity. }
  2: { exact (hrx5_B8I_peer_pure R L NS PS KE T head nk Hinv). }
  unfold hrx5ci_res. rewrite HS1b. change (mident_of x25519 (rr_rawd R)) with (hrx5_ID x25519 R). rewrite Ht.
  (* the accepted peer: its references *)
  destruct (hrx5_B8I_tgt_in _ _ _ _ _ _ _ _ _ Ht) as [sh Hin].
  destruct Hinv as (HF & _). rewrite Forall_forall in HF. specialize (HF _ Hin).
  destruct HF as (_ & _ & _ & _ & _ & Hrefs & _).
  destruct (hrx5_B8I_rc (p_refs P) Hrefs) as (E1 & E2 & E3).
  destruct Hb as (Hrun & Hsec & Hbirth & Hnow).
  destruct Hd as (Hr & _).
  assert (Hrest: forall D1, rx_init_accepted (hrx5_W0 (hrx5_DL x25519 R L sec birth) T PS S w kc lul) D1 S1
    (snd (load_model q lul (s_boot S))) a (hrx5ci_new P M (s_boot S) t ck2 h2) (l_skb L) (sk_len s) =
    mkRW D1 T (supd PS a (hrx5_B8I_put P M (s_boot S) t ck2 h2)) [] S1 w kc
      (snd (load_model q lul (s_boot S))) (hrx5_B8I_log a (l_skb L) (sk_len s))).
  { intros D1. unfold rx_init_accepted. cbn [rw_T rw_PS rw_KS rw_w rw_kc rw_rx hrx5_W0].
    change (p_refs (hrx5ci_new P M (s_boot S) t ck2 h2)) with (rc_add1 (p_refs P)).
    rewrite E1, E2, E3. unfold hrx5_B8I_put, hrx5_B8I_log. reflexivity. }
  rewrite Hrest. clear Hrest.
  assert (HD: forall sec1 birth1, dev_set_cc (hrx5_DL x25519 R L sec birth)
     (mkChk sec1 (cc_ekey (d_cc (hrx5_DL x25519 R L sec birth))) (cc_mkey (d_cc (hrx5_DL x25519 R L sec birth))) birth1
        (cc_dev (d_cc (hrx5_DL x25519 R L sec birth)))) = hrx5_DL x25519 R L sec1 birth1).
  { intros. unfold hrx5_DL, hrx5_D, setup_dev, dev_set_cc. cbn [d_cc cc_ekey cc_mkey cc_dev]. reflexivity. }
  assert (HD0: dev_set_cc (hrx5_DL x25519 R L sec birth) (d_cc (hrx5_DL x25519 R L sec birth)) =
               hrx5_DL x25519 R L sec birth).
  { unfold hrx5_DL, hrx5_D, setup_dev, dev_set_cc. cbn [d_cc]. reflexivity. }
  destruct Hv as [Hv | Hv]; rewrite Hv;
    [| destruct (hrx5_B8I_rot (d_cc (hrx5_DL x25519 R L sec birth)) (s_boot S) (rd_r d)) as [Hq | Hq];
       rewrite Hq].
  - exists sec, birth, S1. rewrite HD0. split; [reflexivity |]. split; [| auto].
    unfold hrx5_base_ok. rewrite HS1b. auto.
  - exists sec, birth, S1. rewrite HD0. split; [reflexivity |]. split; [| auto].
    unfold hrx5_base_ok. rewrite HS1b. auto.
  - exists (rd_r d), (s_boot S), S1. rewrite HD. split; [reflexivity |]. split; [| auto].
    unfold hrx5_base_ok. rewrite HS1b. auto.
Qed.

Lemma hrx5_B8I_path_fwd W q s msg d : hrx5_path W q s msg d = 1 -> hrx5_fwd msg = true.
Proof. unfold hrx5_path. destruct (hrx5_fwd msg); [auto | discriminate]. Qed.

(* branch I's case analysis of the harness's model block *)
Lemma hrx5_B8I_case R NS PS T o now tg ai ar :
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o now tg ai ar -> obj_kind o = 1 -> ai = 1 ->
  hrx5_fwd (obj_bytes o) = true ->
  exists M a P t ck2 h2, o = OInit M /\ ar = 0 /\ tg = hrx5_nfind NS a /\
    hrx5ci_tgt x25519 aead_dec (hrx5_ID x25519 R) PS M now = Some (a, P, t, ck2, h2).
Proof.
  intros Hacc Hk Hai Hf. destruct o as [b|M|M|M]; cbn [obj_kind] in Hk; try discriminate.
  unfold hrx5_acc_ok in Hacc. rewrite Hf in Hacc. destruct Hacc as [Har Hacc].
  destruct (hrx5ci_tgt _ _ _ _ _ _) as [[[[[a P] t] ck2] h2]|] eqn:Ht.
  - destruct Hacc as [_ Htg]. exists M, a, P, t, ck2, h2. auto.
  - destruct Hacc as [Hai' _]. lia.
Qed.

End Model.

(* the log after the accepted initiation passes rx_authenticated(a, sp, 1, 0) *)
Lemma hrx5_B8I_note_same X p : rx_peer X = p -> rx_note X p = X.
Proof.
  destruct X as [c1 c2 c3 c4 c5 c6 c7 c8 c9 c10 c11 c12 x13 x14]; cbn [rx_peer]; intros ->.
  unfold rx_note; cbn [rx_peer].
  destruct (eq_dec p nullval) as [E|E]; [subst; reflexivity |].
  rewrite if_true by reflexivity. reflexivity.
Qed.

Lemma hrx5_B8I_note_new X p : rx_peer X = nullval ->
  rx_note X p = mkRx (rx_cookie X) (rx_cindex X) (rx_endpoint X) (rx_eskb X) (rx_response X) (rx_session X)
    (rx_complete X) (rx_keepalive X) (rx_stats X) (rx_len X) (rx_received X) (rx_traversal X) p (rx_other X).
Proof. intros H. unfold rx_note. rewrite H, if_true by reflexivity. reflexivity. Qed.

Lemma hrx5_B8I_log_eq a sp len :
  hrx5_B8I_log a sp len = mkRx Int.zero Int.zero (inc Int.zero) sp (inc Int.zero) Int.zero Int.zero Int.zero
    (inc Int.zero) (Int64.repr (Int.unsigned len)) (inc Int.zero) (inc Int.zero) a false.
Proof.
  unfold hrx5_B8I_log, rx_tail, rx_auth_traversal, rx_auth_received, rx_update_stats, rx_send_response,
    rx_set_endpoint, rx0.
  cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len
       rx_received rx_traversal rx_peer rx_other].
  repeat match goal with |- context [rx_note ?X ?p] =>
    lazymatch X with
    | context [rx_note _ _] => fail
    | _ => first [ rewrite (hrx5_B8I_note_new X p) by reflexivity
                 | rewrite (hrx5_B8I_note_same X p) by reflexivity ]
    end;
    cbn [rx_cookie rx_cindex rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive rx_stats rx_len
         rx_received rx_traversal rx_peer rx_other]
  end.
  reflexivity.
Qed.

Lemma hrx5_B8I_log_auth a sp len :
  rx_authenticated_b (hrx5_B8I_log a sp len) a sp len Int.one Int.zero = true /\
  rx_peer (hrx5_B8I_log a sp len) = a /\ rx_eskb (hrx5_B8I_log a sp len) = sp.
Proof.
  rewrite hrx5_B8I_log_eq. split; [| split; reflexivity].
  unfold rx_authenticated_b. cbn [rx_cookie rx_endpoint rx_eskb rx_response rx_session rx_complete rx_keepalive
    rx_stats rx_len rx_received rx_traversal rx_peer rx_other].
  rewrite !if_true by reflexivity. rewrite Int64.eq_true. reflexivity.
Qed.

