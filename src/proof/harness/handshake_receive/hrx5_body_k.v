(* law handshake_receive: body proofs of local
   functions of the harness unit (hrx5_spec.v), at the unit's compspecs HRX.  The harness's message builders k_initiation, k_response (K's messages as the model makes them).
*)
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
Require Import WgNoise.proof.harness.handshake_receive.hrx5_k_lib.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_k_lib2.
Local Open Scope logic.

#[local] Existing Instance HRX.

Lemma hrx5_k_peer_fold sh p P : hrx5_k_pok p P ->
  (@field_at HRX sh t_hs (DOT HRC._state) (Vint (hs_state (p_hs P))) (hs_addr p) *
   hbytes sh (hs_ck (p_hs P)) (@field_address HRX t_hs (DOT HRC._chaining_key) (hs_addr p)) *
   hbytes sh (hs_hash (p_hs P)) (@field_address HRX t_hs (DOT HRC._hash) (hs_addr p)) *
   hbytes sh (hs_eph (p_hs P)) (@field_address HRX t_hs (DOT HRC._ephemeral_private) (hs_addr p)) *
   hbytes sh (hs_psk (p_hs P)) (@field_address HRX t_hs (DOT HRC._preshared_key) (hs_addr p)) *
   hrx5_k_prest sh p P |-- peer_rep sh p P)%logic.
Proof. intros Hp. rewrite hrx5_k_peer_open. entailer!. Qed.

Lemma hrx5_k_tai64n_len a b : Zlength (tai64n a b) = 12.
Proof. unfold tai64n, be64, be32. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

Lemma hrx5_body_k_initiation x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_k_initiation
    hrx5_k_initiation_spec.
Proof.
  intros Hx Ha Hxa.
  start_function. hrx5_k_hide_cs.
  assert (SHk: writable_share shk) by assumption.
  set (sc := Share.glb Share.Rsh shi).
  rewrite (@hrx5_k_tuchar__cs HRX CSw Tsh 32 v_eraw).
  forward_call (v_eraw, 32, Tsh). Intros er.
  rewrite (@hrx5_k_tuchar_cs CSw HRX), (hrx5_k_nd er 32 v_eraw) by tauto.
  forward_call (gv, S, w). Intros sn. destruct sn as [sec ns]. simpl fst in *. simpl snd in *.
  rewrite hrx5_k2_shim_open. Intros.
  forward. forward.
  rewrite <- (hrx5_k_hout Tsh 12 v_ts).
  forward_call (Tsh, v_ts, sec, Int64.repr ns).
  set (S' := shim_set_real S sec (Int64.repr ns)).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k2_shim_open gv S' w))).
  set (TS := tai64n sec (Int64.repr ns)).
  assert (HlT: Zlength TS = 12) by apply hrx5_k_tai64n_len.
  assert (HlE: Zlength (map Byte.repr er) = 32) by (rewrite Zlength_map; tauto).
  rewrite (hrx5_k_mident_split shi IK ik H0), (hrx5_k_mident_split shi ID id H2).
  assert_PROP (@field_compatible HRX t_mident [] ik /\ @field_compatible HRX t_mident [] id) as Hfi.
  { entailer!. split.
    - match goal with Hc: field_compatible t_mident (DOT HRC._priv) ik |- _ =>
        apply field_compatible_cons in Hc; exact (proj2 Hc) end.
    - match goal with Hc: field_compatible t_mident (DOT HRC._priv) id |- _ =>
        apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
  destruct Hfi as [Hfik Hfid].
  assert (Hfik1: @field_compatible HRX t_mident (DOT HRC._pub) ik) by auto with field_compatible.
  assert (Hfid1: @field_compatible HRX t_mident (DOT HRC._pub) id) by auto with field_compatible.
  destruct (hrx5_k_hsplit sc shi (mi_pub IK) (field_address t_mident [StructField HRC._pub] ik)
    (hrx5_k_sub_l shi)) as [r1 E1].
  destruct (hrx5_k_hsplit sc shi (mi_pub ID) (field_address t_mident [StructField HRC._pub] id)
    (hrx5_k_sub_l shi)) as [r2 E2].
  destruct (hrx5_k_hsplit sc shk SSK sk (hrx5_k_sub_w shi shk SHk)) as [r3 E3].
  destruct (hrx5_k_hsplit sc Tsh (map Byte.repr er) v_eraw (hrx5_k_sub_T sc)) as [r4 E4].
  destruct (hrx5_k_hsplit sc Tsh TS v_ts (hrx5_k_sub_T sc)) as [r5 E5].
  rewrite E1, E2, E3, E4, E5.
  rewrite hrx5_k2_minit_cs0.
  unfold wg_consts, hrx5_consts.
  forward_call (gv, Tsh, v_mi, sc, field_address t_mident (DOT HRC._pub) ik, mi_pub IK,
                field_address t_mident (DOT HRC._pub) id, mi_pub ID, sk, SSK, v_eraw, map Byte.repr er, v_ts, TS).
  { cancel. }
  { apply hrx5_k_rd; exact SH0. }
  sep_apply (derives_refl' _ _ (eq_sym E1)).
  sep_apply (derives_refl' _ _ (eq_sym E2)).
  sep_apply (derives_refl' _ _ (eq_sym E3)).
  sep_apply (derives_refl' _ _ (eq_sym E4)).
  sep_apply (derives_refl' _ _ (eq_sym E5)).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k_mident_split shi IK ik H0))).
  sep_apply (derives_refl' _ _ (eq_sym (hrx5_k_mident_split shi ID id H2))).
  sep_apply (hrx5_k_hb_out Tsh (map Byte.repr er) v_eraw). rewrite HlE, hrx5_k_hout.
  sep_apply (hrx5_k_hb_out Tsh TS v_ts). rewrite HlT, hrx5_k_hout.
  remember (m_create_initiation_model x25519 aead_enc (mi_pub IK) (mi_pub ID) SSK (map Byte.repr er) TS)
    as ci eqn:Hci.
  forward_if (EX M': init_msg,
    PROP (im_ok M')
    LOCAL (lvar HRC._ts (tarray tuchar 12) v_ts; lvar HRC._eraw (tarray tuchar 32) v_eraw;
      lvar HRC._mi (Tstruct HRC._m_initiation noattr) v_mi;
      gvars gv; temp HRC._m m; temp HRC._ik ik; temp HRC._id id; temp HRC._ss_k sk)
    SEP (data_at_ Tsh (tarray tuchar 12) v_ts; data_at_ Tsh (tarray tuchar 32) v_eraw;
      data_at_ Tsh (Tstruct HRC._m_initiation noattr) v_mi;
      init_rep shm m M'; data_at shi t_mident (mident_val IK) ik; data_at shi t_mident (mident_val ID) id;
      hbytes shk SSK sk; shim_state4 gv S' w; wg_consts gv; hrx5_consts gv)).
  - destruct ci as [[[[[[E encs] enct] ep] ck] h] |]; [| contradiction].
    destruct (hrx5_k2_cinit_len x25519 aead_enc aead_dec _ _ _ _ _ E encs enct ep ck h Hx Ha H0 HlT (eq_sym Hci)) as (HlE2 & HlS & HlT2).
    unfold init_rep. Intros. destruct M as [ty se eph0 encs0 enct0 mac1 mac2].
    match goal with Hm: im_ok _ |- _ => destruct Hm as (Hl1 & Hl2 & Hl3 & Hl4 & Hl5) end.
    cbn [im_eph im_encs im_enct im_mac1 im_mac2] in *.
    rewrite (hrx5_k2_init_split shm ty se eph0 encs0 enct0 mac1 mac2 m Hl1 Hl2 Hl3).
    rewrite (hrx5_k2_minit_split Tsh E encs enct ep ck h v_mi HlE2 HlS HlT2). Intros.
    assert_PROP (field_compatible t_init [] m /\ field_compatible t_minit [] v_mi) as Hf.
    { go_lower. saturate_local. apply prop_right. split.
      - match goal with Hc: field_compatible t_init (DOT HRC._macs) m |- _ =>
          apply field_compatible_cons in Hc; exact (proj2 Hc) end.
      - match goal with Hc: field_compatible t_minit (DOT HRC._st) v_mi |- _ =>
          apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
    destruct Hf as [Hfm Hfmi].
    sep_apply (hrx5_k_hb_out shm eph0 (field_address t_init [StructField HRC._unencrypted_ephemeral] m)).
    rewrite Hl1.
    forward_call (shm, field_address t_init [StructField HRC._unencrypted_ephemeral] m, Tsh,
                  field_address t_minit [StructField HRC._ephemeral] v_mi, E).
    { rewrite HlE2. entailer!.
      all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite HlE2. cancel. }
    sep_apply (hrx5_k_hb_out shm encs0 (field_address t_init [StructField HRC._encrypted_static] m)).
    rewrite Hl2.
    forward_call (shm, field_address t_init [StructField HRC._encrypted_static] m, Tsh,
                  field_address t_minit [StructField HRC._enc_static] v_mi, encs).
    { rewrite HlS. entailer!.
      all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite HlS. cancel. }
    sep_apply (hrx5_k_hb_out shm enct0 (field_address t_init [StructField HRC._encrypted_timestamp] m)).
    rewrite Hl3.
    forward_call (shm, field_address t_init [StructField HRC._encrypted_timestamp] m, Tsh,
                  field_address t_minit [StructField HRC._enc_timestamp] v_mi, enct).
    { rewrite HlT2. entailer!.
      all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite HlT2. cancel. }
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_k2_minit_split Tsh E encs enct ep ck h v_mi HlE2 HlS HlT2))).
    sep_apply (@data_at_data_at_ HCS Tsh t_minit (minit_val E encs enct ep ck h) v_mi).
    rewrite <- hrx5_k2_minit_cs0.
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_k2_init_split shm ty se E encs enct mac1 mac2 m HlE2 HlS HlT2))).
    Exists (mkIM ty se E encs enct mac1 mac2).
    unfold init_rep, wg_consts, hrx5_consts. entailer!.
    unfold im_ok; simpl; repeat split; auto.
  - destruct ci as [[[[[[E encs] enct] ep] ck] h] |]; [discriminate |].
    forward. Exists M.
    rewrite <- hrx5_k2_minit_cs0.
    unfold init_rep, wg_consts, hrx5_consts. entailer!.
  - Intros M'. Exists M' sec ns. unfold S'. entailer!.
Qed.

Lemma hrx5_body_k_response x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs) :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_k_response
    hrx5_k_response_spec.
Proof.
  intros Hx Ha Hxa.
  start_function. hrx5_k_hide_cs.
  forward_call tt. Intros b.
  set (bb := negb (Int.eq (Int.and (Int.repr b) (Int.repr 1)) Int.zero)).
  forward_if (EX idx: int,
    PROP (bb = true -> ~ In (hs_addr p) (t_L T) -> t_fresh T (hs_addr p) idx)
    LOCAL (lvar HRC._ei (tarray tuchar 32) v_ei; lvar HRC._eraw (tarray tuchar 32) v_eraw;
      lvar HRC._cur (Tstruct HRC._m_state noattr) v_cur; lvar HRC._mr (Tstruct HRC._m_response noattr) v_mr;
      gvars gv; temp HRC._m m; temp HRC._h (hs_addr p); temp HRC._t tab; temp HRC._id id)
    SEP (data_at_ Tsh (tarray tuchar 32) v_ei; data_at_ Tsh (tarray tuchar 32) v_eraw;
      data_at_ Tsh (Tstruct HRC._m_state noattr) v_cur; data_at_ Tsh (Tstruct HRC._m_response noattr) v_mr;
      resp_rep shm m M;
      peer_rep shp p (if bb then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P);
      itable sht tab (if andb bb (negb (vin (hs_addr p) (t_L T))) then t_insert T (hs_addr p) idx else T);
      data_at shi t_mident (mident_val ID) id;
      shim_state4 gv (if andb bb (negb (vin (hs_addr p) (t_L T))) then shim_u32 S idx else S) w;
      wg_consts gv; hrx5_consts gv)).
  - (* the handshake made one that waits for a response *)
    assert (Hbb: bb = true) by (unfold bb; rewrite Int.eq_false by auto; reflexivity).
    rewrite hrx5_k_peer_open. Intros.
    match goal with Hc: hrx5_k_pok _ _ |- _ => rename Hc into Hpok end.
    pose proof Hpok as (Hfp & Hok & Hfh).
    forward.
    unfold itable. Intros.
    match goal with Hw: itable_wf T |- _ => pose proof Hw as (HwL & HwI & HwD & HwS) end.
    destruct (hrx5_k_focus (t_L T) (t_D T) (hs_addr p) H HwS) as (she & E0 & Rst & Hrd & Heq2).
    rewrite Heq2. Intros.
    rewrite <- (hrx5_k_entry_fld she (entry_val E0 (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) Hfh).
    forward.
    { entailer!. destruct (vin (hs_addr p) (t_L T)); simpl; auto. }
    rewrite (hrx5_k_entry_fld she (entry_val E0 (succ_in (t_L T) (hs_addr p)) (vin (hs_addr p) (t_L T))) (hs_addr p) Hfh).
    sep_apply (derives_refl' _ _ (eq_sym Heq2)).
    forward_if.
    + (* not hashed: inserted *)
      assert (Hv: vin (hs_addr p) (t_L T) = false).
      { match goal with Ht: typed_true _ _ |- _ => revert Ht end.
        destruct (vin (hs_addr p) (t_L T)); [cbv; discriminate | reflexivity]. }
      rewrite Hv.
      forward_call (gv, S, w, sht, tab, T, hs_addr p, @None (share * entry)).
      { unfold itable, raw_rep. entailer!. }
      Intros idx. Exists idx. rewrite Hbb. cbn [andb negb raw_add].
      rewrite hrx5_k_peer_open. entailer!.
      rewrite Hv, hrx5_k_prest_state. cbn [negb p_hs p_set_hs hs_ck hs_hash hs_eph hs_psk hs_set_state].
      cancel.
    + (* already hashed *)
      assert (Hv: vin (hs_addr p) (t_L T) = true).
      { match goal with Ht: typed_false _ _ |- _ => revert Ht end.
        destruct (vin (hs_addr p) (t_L T)); [reflexivity | cbv; discriminate]. }
      forward. Exists Int.zero. rewrite Hbb, Hv. cbn [andb negb].
      rewrite hrx5_k_peer_open. unfold itable. entailer!.
      { exfalso. match goal with Hn: ~ In _ _ |- _ => apply Hn end.
        unfold vin in Hv. destruct (in_dec _ _ _); [assumption | discriminate]. }
      rewrite hrx5_k_prest_state. cbn [negb p_hs p_set_hs hs_ck hs_hash hs_eph hs_psk hs_set_state].
      cancel.
  - assert (Hbb: bb = false).
    { unfold bb. match goal with Hc: Int.and _ _ = Int.zero |- _ => rewrite Hc end. reflexivity. }
    forward. Exists Int.zero. rewrite Hbb. cbn [andb]. entailer!.
  - Intros idx.
    match goal with Hc: bb = true -> _ |- _ => rename Hc into Hfr end.
    remember (if bb then p_set_hs P (hs_set_state (p_hs P) HS_CREATED_INITIATION) else P) as P1 eqn:HP1.
    remember (if andb bb (negb (vin (hs_addr p) (t_L T))) then t_insert T (hs_addr p) idx else T) as T1 eqn:HT1.
    remember (if andb bb (negb (vin (hs_addr p) (t_L T))) then shim_u32 S idx else S) as S1 eqn:HS1.
    assert (HinT1: In (hs_addr p) (saddrs (t_D T1))).
    { subst T1. destruct (andb _ _); [rewrite hrx5_k_insert_saddrs |]; exact H. }
    rewrite hrx5_k_peer_open. Intros.
    match goal with Hc: hrx5_k_pok _ _ |- _ => rename Hc into Hpok end.
    pose proof Hpok as (Hfp & Hok & Hfh).
    pose proof Hok as (Le & Lrs & Lre & Lss & Lpsk & Lh & Lck & Lts).
    assert_PROP (@field_compatible HRX t_mstate [] v_cur /\ @field_compatible HRX t_mresp [] v_mr) as Hfc
      by entailer!.
    destruct Hfc as [Hfc Hfr2].
    rewrite (@hrx5_k_tuchar__cs HRX CSw Tsh 32 v_eraw).
    forward_call (v_eraw, 32, Tsh). Intros er.
    rewrite (@hrx5_k_tuchar_cs CSw HRX), (hrx5_k_nd er 32 v_eraw) by tauto.
    rewrite (hrx5_k_mstate_split Tsh v_cur).
    forward_call (Tsh, field_address t_mstate (DOT HRC._ck) v_cur, shp,
                  field_address t_hs (DOT HRC._chaining_key) (hs_addr p), hs_ck (p_hs P1)).
    { entailer!. rewrite Lck. simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite Lck. cancel. }
    forward_call (Tsh, field_address t_mstate (DOT HRC._h) v_cur, shp,
                  field_address t_hs (DOT HRC._hash) (hs_addr p), hs_hash (p_hs P1)).
    { entailer!. rewrite Lh. simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
    { rewrite Lh. cancel. }
    unfold hrx5_consts.
    change (hc_const gv HRC._x_handshake_receive__M_BASEPOINT basepoint9)
      with (hbytes Ers basepoint9 (gv HRC._x_handshake_receive__M_BASEPOINT)).
    rewrite <- (hrx5_k_hout Tsh 32 v_ei).
    forward_call (Tsh, v_ei, shp, field_address t_hs (DOT HRC._ephemeral_private) (hs_addr p), hs_eph (p_hs P1),
                  Ers, gv HRC._x_handshake_receive__M_BASEPOINT, basepoint9).
    { cancel. }
    change (hbytes Ers basepoint9 (gv HRC._x_handshake_receive__M_BASEPOINT))
      with (hc_const gv HRC._x_handshake_receive__M_BASEPOINT basepoint9).
    assert (HlD: Zlength (x25519 (hs_eph (p_hs P1)) basepoint9) = 32) by apply Hx.
    assert (HlE: Zlength (map Byte.repr er) = 32) by (rewrite Zlength_map; tauto).
    sep_apply (hrx5_k_mstate_join Tsh (hs_ck (p_hs P1)) (hs_hash (p_hs P1)) v_cur Lck Lh).
    set (sc := Share.glb Share.Rsh shi).
    destruct (hrx5_k_hsplit sc Tsh (x25519 (hs_eph (p_hs P1)) basepoint9) v_ei (hrx5_k_sub_T sc)) as [r1 E1].
    destruct (hrx5_k_hsplit sc Tsh (map Byte.repr er) v_eraw (hrx5_k_sub_T sc)) as [r2 E2].
    destruct (hrx5_k_hsplit sc shi (mi_pub ID) (field_address t_mident [StructField HRC._pub] id)
      (hrx5_k_sub_l shi)) as [r3 E3].
    destruct (hrx5_k_hsplit sc shp (hs_psk (p_hs P1)) (field_address t_hs (DOT HRC._preshared_key) (hs_addr p))
      (hrx5_k_sub_w shi shp SH0)) as [r4 E4].
    rewrite (hrx5_k_mident_split shi ID id H1).
    assert_PROP (@field_compatible HRX t_mident [] id) as Hfi.
    { entailer!. match goal with Hc: field_compatible t_mident (DOT HRC._priv) id |- _ =>
        apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
    assert (Hfi1: @field_compatible HRX t_mident (DOT HRC._pub) id) by auto with field_compatible.
    assert (Hfh1: @field_compatible HRX t_hs (DOT HRC._preshared_key) (hs_addr p)) by auto with field_compatible.
    rewrite E1, E2, E3, E4.
    rewrite hrx5_k_mresp_cs0.
    unfold wg_consts.
    forward_call (gv, Tsh, v_mr, Tsh, v_cur, hs_ck (p_hs P1), hs_hash (p_hs P1), sc, v_ei,
                  x25519 (hs_eph (p_hs P1)) basepoint9, field_address t_mident (DOT HRC._pub) id,
                  mi_pub ID, field_address t_hs (DOT HRC._preshared_key) (hs_addr p),
                  hs_psk (p_hs P1), v_eraw, map Byte.repr er).
    { cancel. }
    { apply hrx5_k_rd; exact SH2. }
    sep_apply (derives_refl' _ _ (eq_sym E1)).
    sep_apply (derives_refl' _ _ (eq_sym E2)).
    sep_apply (derives_refl' _ _ (eq_sym E3)).
    sep_apply (derives_refl' _ _ (eq_sym E4)).
    sep_apply (derives_refl' _ _ (eq_sym (hrx5_k_mident_split shi ID id H1))).
    sep_apply (hrx5_k_hb_out Tsh (x25519 (hs_eph (p_hs P1)) basepoint9) v_ei). rewrite HlD, hrx5_k_hout.
    sep_apply (hrx5_k_hb_out Tsh (map Byte.repr er) v_eraw). rewrite HlE, hrx5_k_hout.
    sep_apply (@data_at_data_at_ HCS Tsh t_mstate (mstate_val (hs_ck (p_hs P1)) (hs_hash (p_hs P1))) v_cur).
    rewrite <- hrx5_k_mstate_cs.
    sep_apply (hrx5_k_peer_fold shp p P1 Hpok).
    remember (m_create_response_model x25519 aead_enc (hs_ck (p_hs P1)) (hs_hash (p_hs P1))
                (x25519 (hs_eph (p_hs P1)) basepoint9) (mi_pub ID) (hs_psk (p_hs P1))
                (map Byte.repr er)) as cr eqn:Hcr.
    forward_if (EX M': resp_msg,
      PROP (rm_ok M')
      LOCAL (lvar HRC._ei (tarray tuchar 32) v_ei; lvar HRC._eraw (tarray tuchar 32) v_eraw;
        lvar HRC._cur (Tstruct HRC._m_state noattr) v_cur; lvar HRC._mr (Tstruct HRC._m_response noattr) v_mr;
        gvars gv; temp HRC._m m; temp HRC._h (hs_addr p); temp HRC._t tab; temp HRC._id id)
      SEP (data_at_ Tsh (tarray tuchar 32) v_ei; data_at_ Tsh (tarray tuchar 32) v_eraw;
        data_at_ Tsh (Tstruct HRC._m_state noattr) v_cur; data_at_ Tsh (Tstruct HRC._m_response noattr) v_mr;
        resp_rep shm m M'; peer_rep shp p P1; itable sht tab T1; data_at shi t_mident (mident_val ID) id;
        shim_state4 gv S1 w; wg_consts gv; hrx5_consts gv)).
    + destruct cr as [[[[[E encn] ep] ck2] h2] |]; [| contradiction].
      destruct (hrx5_k_cresp_len _ _ _ _ _ _ _ _ _ _ _ _ _ _ Hx Ha (eq_sym Hcr)) as [HlE2 HlN].
      unfold resp_rep. Intros. destruct M as [ty se re eph0 encn0 mac1 mac2].
      match goal with Hm: rm_ok _ |- _ => destruct Hm as (Hl1 & Hl2 & Hl3 & Hl4) end.
      cbn [rm_eph rm_encn rm_mac1 rm_mac2] in *.
      rewrite (hrx5_k_resp_split shm ty se re eph0 encn0 mac1 mac2 m Hl1 Hl2).
      rewrite (hrx5_k_mresp_split Tsh E encn ep ck2 h2 v_mr HlE2 HlN). Intros.
      assert_PROP (field_compatible t_resp [] m) as Hfm.
      { entailer!. match goal with Hc: field_compatible t_resp (DOT HRC._macs) m |- _ =>
          apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
      unfold itable. Intros.
      match goal with Hw: itable_wf T1 |- _ => pose proof Hw as (HwL & HwI & HwD & HwS) end.
      destruct (hrx5_k_focus (t_L T1) (t_D T1) (hs_addr p) HinT1 HwS) as (she & E0 & Rst & Hrd & Heq2).
      rewrite Heq2. Intros.
      rewrite <- (hrx5_k_entry_fld she (entry_val E0 (succ_in (t_L T1) (hs_addr p)) (vin (hs_addr p) (t_L T1))) (hs_addr p) Hfh).
      forward. forward.
      rewrite (hrx5_k_entry_fld she (entry_val E0 (succ_in (t_L T1) (hs_addr p)) (vin (hs_addr p) (t_L T1))) (hs_addr p) Hfh).
      sep_apply (derives_refl' _ _ (eq_sym Heq2)).
      sep_apply (hrx5_k_hb_out shm eph0 (field_address t_resp [StructField HRC._unencrypted_ephemeral] m)).
      rewrite Hl1.
      forward_call (shm, field_address t_resp [StructField HRC._unencrypted_ephemeral] m, Tsh,
                    field_address t_mresp [StructField HRC._ephemeral] v_mr, E).
      { rewrite HlE2. entailer!.
        all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
      { rewrite HlE2. cancel. }
      sep_apply (hrx5_k_hb_out shm encn0 (field_address t_resp [StructField HRC._encrypted_nothing] m)).
      rewrite Hl2.
      forward_call (shm, field_address t_resp [StructField HRC._encrypted_nothing] m, Tsh,
                    field_address t_mresp [StructField HRC._enc_nothing] v_mr, encn).
      { rewrite HlN. entailer!.
        all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
      { rewrite HlN. cancel. }
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_k_mresp_split Tsh E encn ep ck2 h2 v_mr HlE2 HlN))).
      sep_apply (@data_at_data_at_ HCS Tsh t_mresp (mresp_val E encn ep ck2 h2) v_mr).
      rewrite <- hrx5_k_mresp_cs0.
      sep_apply (derives_refl' _ _ (eq_sym (hrx5_k_resp_split shm ty se (e_index E0) E encn mac1 mac2 m HlE2 HlN))).
      Exists (mkRM ty se (e_index E0) E encn mac1 mac2).
      unfold resp_rep, itable, wg_consts, hrx5_consts. entailer!.
      unfold rm_ok; simpl; repeat split; auto.
    + destruct cr as [[[[[E encn] ep] ck2] h2] |]; [discriminate |].
      forward. Exists M. Intros ab.
      match goal with |- context [@data_at HCS Tsh t_mresp ?v v_mr] =>
        sep_apply (@data_at_data_at_ HCS Tsh t_mresp v v_mr) end.
      rewrite <- hrx5_k_mresp_cs0.
      unfold resp_rep, wg_consts, hrx5_consts. entailer!.
    + Intros M'. Exists M' bb idx. subst P1 T1 S1. entailer!.
Qed.

(* the conjunction of this file's body lemmas *)
Definition hrx5_bodies_k : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_k_initiation hrx5_k_initiation_spec) /\
  (@semax_body hrx5_V (hrx5_Gl x25519 aead_enc aead_dec xaead_enc xaead_dec CSw HRX) HRX HRC.f_k_response hrx5_k_response_spec).

Theorem hrx5_grp_k : hrx5_bodies_k.
Proof.
  intros x25519 aead_enc aead_dec xaead_enc xaead_dec CSw H1 H2 H3.
  exact (conj (hrx5_body_k_initiation _ _ _ _ _ _ H1 H2 H3)
    (hrx5_body_k_response _ _ _ _ _ _ H1 H2 H3)).
Qed.
