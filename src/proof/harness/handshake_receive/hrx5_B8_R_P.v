(* law handshake_receive: phase B8, branch R: the
   pure statement hrx5_B8R_P_stmt. *)
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
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

Local Open Scope Z_scope.

Lemma hrx5_B8RP_le32 v : le32_val (le32 v) = v.
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

Lemma hrx5_B8RP_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (H1 & H2 & H3 & H4). unfold resp_bytes, le32. autorewrite with sublist.
  rewrite H1, H2, H3, H4. reflexivity.
Qed.

Lemma hrx5_B8RP_rm_of M : rm_ok M -> rm_of (resp_bytes M) = M.
Proof.
  intros (H1 & H2 & H3 & H4). destruct M as [ty snd rcv eph encn m1 m2]; cbn [rm_eph rm_encn rm_mac1 rm_mac2] in *.
  unfold rm_of, resp_bytes; cbn [rm_type rm_sender rm_receiver rm_eph rm_encn rm_mac1 rm_mac2].
  assert (L4: forall v, Zlength (le32 v) = 4) by reflexivity.
  pose proof (L4 ty) as Lty. pose proof (L4 snd) as Lsn. pose proof (L4 rcv) as Lrc.
  f_equal.
  - rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8RP_le32.
  - rewrite sublist_app2 by (try rewrite L4; lia). rewrite L4. simpl Z.sub.
    rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8RP_le32.
  - rewrite sublist_app2 by (try rewrite L4; lia). rewrite L4. simpl Z.sub.
    rewrite sublist_app2 by (try rewrite L4; lia). rewrite L4. simpl Z.sub.
    rewrite sublist_app1 by (try rewrite L4; lia). rewrite sublist_same by (try rewrite L4; lia).
    apply hrx5_B8RP_le32.
  - list_solve.
  - list_solve.
  - list_solve.
  - list_solve.
Qed.

Lemma hrx5_B8RP_tw M : hrx5_tw (resp_bytes M) = rm_type M.
Proof.
  unfold hrx5_tw, resp_bytes. rewrite sublist_app1 by (cbn; list_solve).
  rewrite sublist_same by reflexivity. apply hrx5_B8RP_le32.
Qed.

Lemma hrx5_B8RP_fwd_type M : rm_ok M -> hrx5_fwd (resp_bytes M) = true -> rm_type M = Int.repr 2.
Proof.
  intros Hok. unfold hrx5_fwd. rewrite hrx5_B8RP_len, hrx5_B8RP_tw by exact Hok.
  cbn [Z.leb Z.eqb Pos.eqb Z.compare Pos.compare Pos.compare_cont andb orb].
  rewrite !andb_false_r, !orb_false_r, andb_true_r. rewrite orb_false_l.
  intros H. pose proof (Int.eq_spec (rm_type M) (Int.repr 2)) as E. rewrite H in E. exact E.
Qed.

Lemma hrx5_B8RP_path_fwd W q s msg d : hrx5_path W q s msg d = 1 -> hrx5_fwd msg = true.
Proof. unfold hrx5_path. destruct (hrx5_fwd msg); [auto | discriminate]. Qed.

(* the first node of the peer a is at the index of the first peer at a *)
Lemma hrx5_B8RP_index {dP: Inhabitant (val * share * peer)} {dN: Inhabitant hnode4} PS NS a sh P :
  sfind PS a = Some (sh, P) -> map hn_p NS = map peer_addr4 PS ->
  exists j, 0 <= j < Zlength PS /\ Znth j PS = (a, sh, P) /\ hn_p (Znth j NS) = a /\
    hrx5_nfind NS a = hn_addr (Znth j NS).
Proof.
  revert NS. induction PS as [| [[x shx] vx] PS IH]; intros NS Hf Hm; cbn [sfind] in Hf; [discriminate |].
  destruct NS as [| N NS]; cbn [map] in Hm; [discriminate |]. cbn [peer_addr4] in Hm. injection Hm as Hx Hm'.
  cbn [hrx5_nfind].
  destruct (eq_dec x a) as [E | E].
  - subst x. inversion Hf; subst sh P. exists 0. rewrite !Znth_0_cons. rewrite Zlength_cons.
    split; [pose proof (Zlength_nonneg PS); lia |]. split; [reflexivity |]. split; [exact Hx |].
    rewrite if_true by exact Hx. reflexivity.
  - destruct (IH NS Hf Hm') as (j & Hj & HZ & Hp & Hn). exists (j + 1).
    rewrite Zlength_cons. rewrite !Znth_pos_cons by lia. replace (j + 1 - 1) with j by lia.
    split; [lia |]. split; [exact HZ |]. split; [exact Hp |].
    rewrite if_false by (rewrite Hx; exact E). exact Hn.
Qed.

Section Model.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* hrx5cr_agree for any raw private key (D's) *)
Lemma hrx5_B8RP_agree raw T KA PS M :
  peers_refs_ok PS -> hrx5cr_pool KA PS T ->
  consume_response_model x25519 aead_dec (setup_identity x25519 raw) T PS M =
  match hrx5cr_tgt x25519 aead_dec (mident_of x25519 raw) T PS M with
  | Some (a, P, ck, h) => Some (a, hrx5cr_new P M ck h)
  | None => None
  end.
Proof.
  intros HR HP.
  unfold consume_response_model, hrx5cr_tgt, setup_identity, identity_of, mident_of, t_lookup.
  cbn [d_id id_has id_priv mi_ok mi_priv].
  destruct (andb (memneq_bool raw zeros32) (memneq_bool (x25519 raw basepoint9) zeros32))
    eqn:Hok; [|reflexivity].
  cbn [negb].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a E]|] eqn:HF; [|reflexivity].
  assert (HT: e_type E = IDX_KEYPAIR \/ e_type E = IDX_HANDSHAKE).
  { apply hrx5cr_model_find_in in HF. unfold t_entry in HF.
    destruct (sfind (t_D T) a) as [[sh E']|] eqn:HS; [|discriminate].
    inv HF. eapply hrx5cr_model_pool_type; [exact HP|]. apply hrx5cr_model_sfind_in; exact HS. }
  destruct HT as [HT|HT]; rewrite HT.
  - reflexivity.
  - change (Int.eq (Int.and IDX_HANDSHAKE IDX_HANDSHAKE) Int.zero) with false.
    change (Int.eq IDX_HANDSHAKE IDX_HANDSHAKE) with true. cbv iota.
    destruct (sfind PS (e_peer E)) as [[sp P]|] eqn:HS; [|reflexivity].
    assert (HRP: 0 < Int.unsigned (p_refs P) < 2147483647).
    { apply hrx5cr_model_sfind_in in HS. unfold peers_refs_ok in HR.
      rewrite Forall_forall in HR. exact (HR _ HS). }
    unfold peer_get.
    replace (Int.eq (p_refs P) Int.zero) with false
      by (symmetry; apply Int.eq_false; intros E0; rewrite E0, Int.unsigned_zero in HRP; lia).
    destruct (Int.eq (hs_state (p_hs P)) HS_CREATED_INITIATION); cbn [negb]; [|reflexivity].
    rewrite hrx5cr_model_crypto.
    destruct (consume_resp_crypto x25519 aead_dec _ (p_hs P) M) as [[ck h]|]; reflexivity.
Qed.

Lemma hrx5_B8RP_tgt_sfind IA T PS M a P ck h :
  hrx5cr_tgt x25519 aead_dec IA T PS M = Some (a, P, ck, h) -> exists sh, sfind PS a = Some (sh, P).
Proof.
  unfold hrx5cr_tgt. destruct (mi_ok IA); [| discriminate].
  destruct (t_find_index T (t_L T) (rm_receiver M)) as [[a0 E]|]; [| discriminate].
  destruct (Int.eq (e_type E) IDX_HANDSHAKE); [| discriminate].
  destruct (sfind PS (e_peer E)) as [[sh P0]|] eqn:Hf; [| discriminate].
  destruct (Int.eq (hs_state (p_hs P0)) HS_CREATED_INITIATION); [| discriminate].
  destruct (m_consume_response_model _ _ _ _ _ _ _ _ _) as [[ck0 h0]|]; [| discriminate].
  intros H; inversion H; subst. eauto.
Qed.

End Model.

Lemma hrx5_B8R_P_ok : hrx5_B8R_P_stmt.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T head nk KE st i kc lul q
    proto ip4 ip6 port o dp tg ai ar d HY Hb Hinv Hst Hi Hok Hmc Hacc Hd (Hpath & Hk & Har).
  unfold hrx5_B8_path in Hpath.
  pose proof (hrx5_B8RP_path_fwd _ _ _ _ _ Hpath) as Hfwd.
  destruct o as [b|M0|M|M0]; cbn [obj_kind] in Hk; try discriminate. clear Hk.
  cbn [obj_bytes obj_ok] in Hfwd, Hok |- *.
  unfold hrx5_acc_ok in Hacc. cbn [obj_bytes] in Hacc. rewrite Hfwd in Hacc. destruct Hacc as [Hai Hacc].
  destruct (hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M) as [[[[a P] ck] h]|] eqn:Ht;
    [| destruct Hacc as [Har' _]; lia].
  destruct Hacc as [_ Htg].
  destruct (hrx5_B8RP_tgt_sfind x25519 aead_dec _ _ _ _ _ _ _ _ Ht) as [sh Hsf].
  pose proof Hinv as (HF & _ & _ & _ & HNP & _ & Hpool).
  pose proof (hrx5cr_model_sfind_in _ _ _ _ Hsf) as Hin.
  assert (Hsh: sh = Ews).
  { rewrite Forall_forall in HF. destruct (HF _ Hin) as (Hs & _). exact Hs. }
  subst sh.
  destruct (hrx5_B8RP_index PS NS a Ews P Hsf HNP) as (j & Hj & HZ & Hp & Hn).
  exists a, P, M, ck, h, j.
  cbn [fold_right hrx5_B8R_facts].
  split; [reflexivity |]. split; [exact Hfwd |]. split; [exact Hai |]. split; [exact Har |].
  split; [exact Ht |]. split; [exact Hj |]. split; [exact HZ |]. split; [exact Hp |].
  split; [rewrite Htg; exact Hn |]. split; [| exact I].
  assert (Hrefs: peers_refs_ok PS).
  { unfold peers_refs_ok. eapply Forall_impl; [| exact HF].
    intros [[p sp] Q] (_ & _ & _ & _ & _ & Hr & _). exact Hr. }
  pose proof (hrx5_B8RP_fwd_type M Hok Hfwd) as Hty.
  change (obj_bytes (OResp M)) with (resp_bytes M) in *.
  unfold hrx5_path in Hpath. rewrite Hfwd, hrx5_B8RP_tw, Hty in Hpath.
  rewrite (Int.eq_false (Int.repr 2) (Int.repr 3)) in Hpath by discriminate.
  unfold hrx5_B8R_W1, rx_model. cbn [obj_bytes]. rewrite Hfwd. unfold rx_packet.
  rewrite hrx5_B8RP_tw, Hty. rewrite (Int.eq_false (Int.repr 2) (Int.repr 3)) by discriminate.
  rewrite (Int.eq_false (Int.repr 2) Int.one) by discriminate.
  cbn [rw_D rw_S rw_lul rw_T rw_PS rw_KS rw_w rw_kc rw_rx hrx5_W0] in Hpath |- *.
  cbv zeta in Hpath |- *.
  destruct (rx_consumes _ _) eqn:Hc; [| destruct (rx_needs_cookie _ _); discriminate].
  rewrite hrx5_B8RP_rm_of by exact Hok.
  unfold cre_res.
  change (d_id (dev_set_cc ?D ?c)) with (d_id D).
  change (d_id (hrx5_DL x25519 R L sec birth)) with (setup_identity x25519 (rr_rawd R)).
  rewrite (hrx5_B8RP_agree x25519 aead_dec (rr_rawd R) T (map ke_addr KE) PS M Hrefs Hpool).
  change (mident_of x25519 (rr_rawd R)) with (hrx5_ID x25519 R). rewrite Ht.
  reflexivity.
Qed.

