(* law create_any: main's body, segment F1b (op == 1 branch, body statement 4: if (s.state == CONSUMED_INITIATION) { the harness's step-by-step model of create_response }). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_conv.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
Require Import WgNoise.proof.libc.libc_bytes.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_defs.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_lib.
Require Import WgNoise.proof.harness.create_any.hca5_F1b_L1.
Require WgNoise.harness.x_create_any.code.

#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_F1b_cceH2 : change_composite_env HCS W_create_any.
Proof. make_cs_preserve HCS W_create_any. Defined.

(* ---- the snapshot struct at the world, with the value typed at the world ---- *)
Definition hca5_F1b_xvalW (s: hsnap) : @reptype W_create_any t_hsnap :=
  let E := sn_entry s in let H := sn_hs s in
  (e_peer E, (sn_next s, (Val.of_bool (sn_hashed s), (Vint (e_type E), (Vint (e_index E),
  (Vint (hs_state H), (Vlong (hs_lic H), (hs_sid H, (bytes (hs_eph H), (bytes (hs_rstatic H),
  (bytes (hs_reph H), (bytes (hs_ss H), (bytes (hs_psk H), (bytes (hs_hash H), (bytes (hs_ck H),
  (bytes (hs_ts H), Vint (hs_rindex H))))))))))))))))).

Lemma hca5_F1b_xW2 sh sn p :
  @data_at HCS sh t_hsnap (hsnap_val sn) p = @data_at W_create_any sh t_hsnap (hca5_F1b_xvalW sn) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_create_any hca5_F1b_cceH2 sh t_hsnap (hsnap_val sn)
    (hca5_F1b_xvalW sn) (@JMeq_refl _ (hsnap_val sn)) ltac:(vm_compute; reflexivity))).
Qed.

Lemma hca5_F1b_snhs T a E H : sn_hs (snap_of T a E H) = H.
Proof. reflexivity. Qed.

Lemma hca5_F1b_resp_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (A & B & C & D). unfold resp_bytes. rewrite !Zlength_app, !hca5_F1b_le32_len, A, B, C, D.
  reflexivity.
Qed.

Lemma hca5_F1b_slog P S1 rr b idx : Zlength rr = 32 -> Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION = true ->
  s_log (hca5_cr_shim P S1 rr b idx) = rr.
Proof.
  intros Hl Hi. unfold hca5_cr_shim. rewrite Hi.
  assert (s_log (shim_draw S1 rr) = rr).
  { unfold shim_draw; cbn [s_log]. rewrite Hl. change (Z.min 32 32) with 32.
    rewrite sublist_same by lia. rewrite sublist_nil, app_nil_r. reflexivity. }
  destruct b; auto.
Qed.

Lemma hca5_F1b_exp_noci x25519 aead_enc H before r u :
  Int.eq (hs_state H) HS_CONSUMED_INITIATION = false ->
  hca3_resp_exp x25519 aead_enc H before r u = (false, before, H).
Proof. intros Hs. unfold hca3_resp_exp. rewrite Hs. reflexivity. Qed.

(* the fields of x the block does not write *)
Lemma hca5_F1b_xrest_res x25519 aead_enc sh T a E H before r u p :
  hca5_F1b_xrest sh (snap_of T a E (snd (hca3_resp_exp x25519 aead_enc H before r u))) p =
  hca5_F1b_xrest sh (snap_of T a E H) p.
Proof.
  unfold hca3_resp_exp; cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end; reflexivity.
Qed.

Lemma hca5_F1b_res_lens x25519 aead_enc H before r u :
  x25519_props x25519 -> hs_ok H -> Zlength r = 32 ->
  let X := snd (hca3_resp_exp x25519 aead_enc H before r u) in
  Zlength (hs_eph X) = 32 /\ Zlength (hs_hash X) = 32 /\ Zlength (hs_ck X) = 32.
Proof.
  intros _ (He & _ & _ & _ & _ & Hh & Hc & _) Hr. unfold hca3_resp_exp; cbv zeta.
  repeat match goal with |- context [if ?b then _ else _] => destruct b end;
    cbn [snd hs_eph hs_hash hs_ck hs_set_eph hs_set_ckh hs_set_state];
    rewrite ?hca5_F1b_clamp_len, ?hca5_F1b_mix_hash_len, ?hca5_F1b_kdf1_len by auto; auto.
Qed.

Lemma hca5_F1b_sclose sh T a E H p : hs_ok H ->
  hbytes sh (hs_rstatic H) (offset_val 80 p) * hbytes sh (hs_reph H) (offset_val 112 p) *
  hbytes sh (hs_psk H) (offset_val 176 p) * hbytes sh (hs_hash H) (offset_val 208 p) *
  hbytes sh (hs_ck H) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._remote_index) (Vint (hs_rindex H)) p *
  hca5_F1b_srest sh (snap_of T a E H) p |-- @data_at_ HCS sh t_hsnap p.
Proof.
  intros Hok. pose proof (hca5_F1b_ssplit sh (snap_of T a E H) p Hok) as Q.
  rewrite hca5_F1b_snhs in Q. rewrite <- Q. apply data_at_data_at_.
Qed.

Lemma hca5_F1b_xclose sh T a E H p :
  Zlength (hs_eph H) = 32 -> Zlength (hs_hash H) = 32 -> Zlength (hs_ck H) = 32 ->
  hbytes sh (hs_eph H) (offset_val 48 p) * hbytes sh (hs_hash H) (offset_val 208 p) *
  hbytes sh (hs_ck H) (offset_val 240 p) *
  @field_at W_create_any sh t_hsnap (DOT HC._state) (Vint (hs_state H)) p *
  hca5_F1b_xrest sh (snap_of T a E H) p |-- @data_at HCS sh t_hsnap (hsnap_val (snap_of T a E H)) p.
Proof.
  intros He Hh Hc. pose proof (hca5_F1b_xsplit sh (snap_of T a E H) p He Hh Hc) as Q.
  rewrite hca5_F1b_snhs in Q. rewrite Q. apply derives_refl.
Qed.

Lemma hca5_F1b_shclose gv S w : Zlength (s_log S) = 32 ->
  hbytes Ews (s_log S) (gv HC._wg_shim_random_log) *
  @data_at W_create_any Ews tuint (Vint (s_u32 S)) (gv HC._wg_shim_random_u32) *
  hca5_F1b_shrest gv S w |-- shim_state4 gv S w.
Proof. intros Hl. rewrite hca5_F1b_shim_split. entailer!. Qed.

Lemma hca5_F1b_fc_W (t: type) gfs p : @field_compatible W_create_any t gfs p -> @field_compatible W_create_any t [] p.
Proof. unfold field_compatible. intros (A & B & C & D & F). repeat split; auto. Qed.

Lemma hca5_F1b_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1S1 x25519 aead_enc gv L FR w m)
    hca5_F1b
    (overridePost (hca5_F1S2 x25519 aead_enc gv L FR w m) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F1S1, hca5_Delta, hca5_R. rewrite hca5_F1b_eq.
  simplify_func_tycontext. abbreviate_semax.
  Intros R P T KS E M S1 rr idx S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
  rewrite (hca5_F1b_xW2 Tsh _ (l_s L)).
  forward.
  match goal with |- context [temp HC._t'46 ?v] => change v with (Vint (hs_state (p_hs P))) end.
  rewrite <- (hca5_F1b_xW2 Tsh _ (l_s L)).
  destruct (Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION) eqn:Hci.
  2: { forward_if.
       { exfalso. unfold HS_CONSUMED_INITIATION in Hci. rewrite H8 in Hci. rewrite Int.eq_true in Hci. discriminate. }
       forward.
       unfold hca5_F1S2.
       Exists R P T KS E M S1 rr idx S0.
       replace (hca5_Y x25519 aead_enc P M S1 rr idx) with (false, resp_bytes M, p_hs P)
         by (unfold hca5_Y; rewrite hca5_F1b_exp_noci by auto; reflexivity).
       unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app fst snd].
       sep_apply (data_at_data_at_ Tsh t_hsnap (hsnap_val (snap_of T (hs_addr (l_p L)) E (p_hs P))) (l_s L)).
       sep_apply (hca5_F1b_hout Tsh (resp_bytes M) 92 (l_before1 L) (hca5_F1b_resp_len M H4)).
       entailer!. }
  forward_if.
  2: { exfalso. unfold HS_CONSUMED_INITIATION in Hci. apply Int.same_if_eq in Hci. rewrite Hci in H8. auto. }
  unfold POSTCONDITION, abbreviate.
  assert (HD: Delta = hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    by (unfold Delta, Delta_specs, abbreviate; reflexivity).
  rewrite HD; clear HD.
  pose proof H0 as (Hdev & Hsid & Hok & _).
  rewrite (hca5_F1b_ssplit Tsh (snap_of T (hs_addr (l_p L)) E (p_hs P)) (l_s L) Hok).
  pose proof Hok as (He & _ & _ & _ & _ & Hh & Hc & _).
  rewrite (hca5_F1b_xsplit Tsh (snap_of T (hs_addr (l_p L)) E (p_hs P)) (l_x L) He Hh Hc).
  rewrite hca5_F1b_shim_split. rewrite !hca5_F1b_snhs. Intros.
  set (S := hca5_CRshim x25519 aead_enc P M S1 rr idx) in *.
  assert_PROP (@field_compatible W_create_any t_hsnap (DOT HC._state) (l_x L)) as FCx0 by entailer!.
  assert_PROP (@field_compatible W_create_any t_hsnap (DOT HC._remote_index) (l_s L)) as FCs0 by entailer!.
  assert_PROP (@field_compatible HCS t_mstate [] (l_st L)) as FCst by entailer!.
  assert (HF: hca5_F1b_facts x25519 aead_enc L (p_hs P) S (resp_bytes M) rr).
  { destruct HH as (X & A & _).
    split; [exact X|]. split; [exact (aead_enc_length _ _ A)|]. split; [exact Hok|]. split; [exact H5|].
    split. { unfold S, hca5_CRshim. apply hca5_F1b_slog; auto. }
    split; [apply hca5_F1b_resp_len; auto|]. split; [exact Hci|].
    split; [exact (hca5_F1b_fc_W _ _ _ FCx0)|]. split; [exact (hca5_F1b_fc_W _ _ _ FCs0)|]. exact FCst. }
  eapply semax_pre; [| eapply semax_post;
    [| | | | apply (hca5_F1b_L1 x25519 aead_enc aead_dec xaead_enc xaead_dec gv L m
               (Val.of_bool (fst (fst (hca5_CR x25519 aead_enc P M rr idx)))) (kents_head KS) (Vint (p_refs P))
               (device_rep Tsh (l_wa L) (hca5_D x25519 R L) * ptable Tsh (l_pta L) (l_p L) *
                @data_at HCS Tsh t_mident (mident_val (hca5_I x25519 R)) (l_ia L) *
                itable Tsh (l_ita L) (if fst (fst (hca5_CR x25519 aead_enc P M rr idx))
                                      then t_insert T (hs_addr (l_p L)) idx else T) *
                peer_rep Tsh (l_p L) (p_set_hs P (snd (hca5_CR x25519 aead_enc P M rr idx))) *
                hca5_rest x25519 L R P T KS S0 w *
                hca5_F1b_srest Tsh (snap_of T (hs_addr (l_p L)) E (p_hs P)) (l_s L) *
                hca5_F1b_xrest Tsh (snap_of T (hs_addr (l_p L)) E (p_hs P)) (l_x L) *
                hca5_tok t_resp_W m * resp_rep Ews m (snd (fst (hca5_CR x25519 aead_enc P M rr idx))) *
                hbytes Tsh (resp_bytes M) (l_before1 L) * mem_mgr gv * hca5_F1b_shrest gv S w *
                noise_globals gv Int64.zero * FR *
                hout Tsh 32 (l_raw L) * hout Tsh 32 (l_pub L) * hout Tsh 32 (l_psk L) *
                hout Tsh 12 (l_ts L) * hout Tsh 1 (l_nothing L) *
                hout Tsh 148 (l_before L) * hout Tsh 148 (l_exp L) * hout Tsh 148 (l_img L) *
                hout Tsh 92 (l_img1 L))
               (p_hs P) S (resp_bytes M) rr HH HF)]].
  - unfold hca5_F1b_S1, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_lvars; cbn [app]. entailer!.
  - rewrite !overridePost_normal'.
    change (hca5_F1b_res x25519 aead_enc (p_hs P) S (resp_bytes M) rr) with (hca5_Y x25519 aead_enc P M S1 rr idx).
    pose proof (hca5_F1b_res_lens x25519 aead_enc (p_hs P) (resp_bytes M) rr (s_u32 S) (proj1 HH) Hok H5)
      as (Le & Lh & Lc).
    change (hca3_resp_exp x25519 aead_enc (p_hs P) (resp_bytes M) rr (s_u32 S))
      with (hca5_Y x25519 aead_enc P M S1 rr idx) in Le, Lh, Lc.
    rewrite <- (hca5_F1b_xrest_res x25519 aead_enc Tsh T (hs_addr (l_p L)) E (p_hs P) (resp_bytes M) rr (s_u32 S)
      (l_x L)).
    change (hca3_resp_exp x25519 aead_enc (p_hs P) (resp_bytes M) rr (s_u32 S))
      with (hca5_Y x25519 aead_enc P M S1 rr idx).
    unfold hca5_F1b_fin, hca5_F1b_Q, hca5_F1b_xs, hca5_F1b_ss, hca5_F1S2.
    Exists R P T KS E M S1 rr idx S0.
    unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
    fold S.
    sep_apply (hca5_F1b_sclose Tsh T (hs_addr (l_p L)) E (p_hs P) (l_s L) Hok).
    sep_apply (hca5_F1b_xclose Tsh T (hs_addr (l_p L)) E (snd (hca5_Y x25519 aead_enc P M S1 rr idx)) (l_x L)
      Le Lh Lc).
    sep_apply (hca5_F1b_shclose gv S w H9).
    sep_apply (hca5_F1b_hout Tsh (resp_bytes M) 92 (l_before1 L) (hca5_F1b_resp_len M H4)).
    entailer!.
  - unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
  - unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
  - intros vl. unfold hca5_R. destruct (frame_ret_assert _ _). simpl. intros; apply andp_left2, derives_refl.
Qed.
