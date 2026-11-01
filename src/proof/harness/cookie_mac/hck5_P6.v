(* law cookie_mac: main's phase P6, statements 69..74 of hck5_cut.v:
   v1 P6 (hck3_P6.v.old) without its last statement (validate).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

(* byte arrays are the same predicate in every compspecs (copy of libc_bytes.v, whose .vo is absent) *)
Section Bytes.
Context {cs1 cs2: compspecs}.

Lemma hck5_p6_align_tuchar: forall (ce: composite_env) n z,
  align_compatible_rec ce (tarray tuchar n) z.
Proof.
  intros. apply align_compatible_rec_Tarray. intros.
  eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l].
Qed.

Lemma hck5_p6_fc_tuchar: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (hck5_p6_align_tuchar (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (hck5_p6_align_tuchar (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hck5_p6_tuchar_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hck5_p6_fc_tuchar.
Qed.

Lemma hck5_p6_tuchar__cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof.
  intros. unfold data_at_, field_at_. apply hck5_p6_tuchar_cs.
Qed.
End Bytes.

Lemma hck5_p6_mods255 k : 0 <= k <= Byte.max_unsigned ->
  Int.mods (Int.repr k) (Int.repr 255) = Int.repr (k mod 255).
Proof.
  intros. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma hck5_p6_zext x : Vint (Int.zero_ext 8 x) = Vubyte (Byte.repr (Int.unsigned (Int.zero_ext 8 x))).
Proof.
  unfold Vubyte. f_equal. pose proof (Int.zero_ext_range 8 x ltac:(rep_lia)).
  change (two_p 8) with 256 in H.
  rewrite Byte.unsigned_repr by rep_lia. symmetry; apply Int.repr_unsigned.
Qed.

Lemma hck5_p6_hbytes_W sh l p :
  hbytes sh l p = @data_at W_cookie_mac sh (tarray tuchar (Zlength l)) (bytes l) p.
Proof. unfold hbytes. apply hck5_p6_tuchar_cs. Qed.

Section P6.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* after the corruption block: msg holds MSG2 (MSG1 unless corrupted) *)
Definition hck5_p6_J (gv: globals) (L: hck5_loc) (FR: mpred) (R: hck5_run) (S: shim) (A: hck5_aval) (m c: val)
  (Q: hck5_pkt) (cmode: bool) (C1: cookie) (MSG1: list byte) : environ -> mpred :=
  EX MSG2: list byte, EX corr: bool,
    PROPx [(corr = false -> MSG2 = MSG1); Zlength MSG2 = q_n Q]
    (LOCALx ([temp HK._corrupted (Vint (if corr then Int.one else Int.zero));
            temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero));
            temp HK._kes (a_kes A); temp HK._head0 (a_head0 A); temp HK._refs0 (Vint (p_refs (a_P A)));
            temp HK._len (Vlong (Int64.repr (q_n Q))); temp HK._msg m; temp HK._copy c;
            temp HK._now (Vlong (q_now Q));
            temp HK._cookie_mode (Vint (if cmode then Int.one else Int.zero))] ++ hck5_lvars gv L)
    (SEPx ([hck5_A x25519 R L A] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
         [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC2 x25519 R L (q_now Q) cmode);
          cookie_rep Tsh (cookie_addr (l_p L)) C1;
          skb_rep Tsh (l_skb L) (hck5_skb Q m);
          hck5_tok (q_n Q) m; hbytes Ews MSG2 m; hck5_tok (q_n Q) c; hbytes Ews MSG1 c;
          hout Tsh 32 (l_secret L)] ++
         hck5_scr2 L ++ hck5_snaps0 L ++ hck5_globs gv S FR))).

#[local] Instance hck5_p6_CCE : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

Lemma hck5_p6_fc_dev wb : @field_compatible Noise.CS t_dev [] wb -> @field_compatible W_cookie_mac t_dev [] wb.
Proof. intros. apply (@field_compatible_change_composite Noise.CS W_cookie_mac _ t_dev); [reflexivity | auto]. Qed.

Lemma hck5_p6_fc_cc wb : @field_compatible Noise.CS t_dev [] wb -> @field_compatible Noise.CS t_cc [] (cc_addr wb).
Proof.
  intros FC.
  assert (F1: @field_compatible Noise.CS t_dev (DOT I._cookie_checker) wb) by auto with field_compatible.
  pose proof (@field_compatible_nested_field Noise.CS t_dev (DOT I._cookie_checker) wb F1) as F2.
  unfold cc_addr, OFS_DEV_CHECKER. exact F2.
Qed.
Lemma hck5_p6_sb_eq sh wb (v: val) : @field_compatible Noise.CS t_dev [] wb ->
  @field_at Noise.CS sh t_cc (DOT I._secret_birthdate) v (cc_addr wb) =
  @field_at W_cookie_mac sh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) v wb.
Proof.
  intros FC. pose proof (hck5_p6_fc_cc wb FC) as FCC. pose proof (hck5_p6_fc_dev wb FC) as FCW.
  rewrite (@field_at_data_at Noise.CS), (@field_at_data_at W_cookie_mac).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  rewrite (@field_address_offset W_cookie_mac) by auto with field_compatible.
  unfold cc_addr, OFS_DEV_CHECKER. rewrite offset_offset_val. simpl.
  exact (f_equal (fun f => f _) (@data_at_change_composite Noise.CS W_cookie_mac _ sh tulong v v (JMeq_refl v) eq_refl)).
Qed.

(* B's checker without its secret and birthdate *)
Definition hck5_p6_ccrest (sh: share) (c: val) (CC: checker) (lk: val) : mpred :=
  (@field_at Noise.CS sh t_cc (DOT I._cookie_encryption_key) (bytes (cc_ekey CC)) c *
  @field_at Noise.CS sh t_cc (DOT I._message_mac1_key) (bytes (cc_mkey CC)) c *
  @field_at Noise.CS sh t_cc (DOT I._secret_lock) lk c *
  spacer sh 108 112 c *
  @field_at Noise.CS sh t_cc (DOT I._device) (cc_dev CC) c)%logic.

Lemma hck5_p6_cc_open sh wb CC lk (V: @reptype Noise.CS t_cc) :
  @field_compatible Noise.CS t_dev [] wb -> Zlength (cc_secret CC) = 32 ->
  V = (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC), (Vlong (cc_birth CC), (lk, cc_dev CC))))) ->
  (@data_at Noise.CS sh t_cc V (cc_addr wb) =
  hbytes sh (cc_secret CC) (cc_addr wb) *
  @field_at W_cookie_mac sh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) (Vlong (cc_birth CC)) wb *
  hck5_p6_ccrest sh (cc_addr wb) CC lk)%logic.
Proof.
  intros FC HL HV; subst V. pose proof (hck5_p6_fc_cc wb FC) as FCC.
  rewrite <- hck5_p6_sb_eq by auto.
  unfold hck5_p6_ccrest, t_cc.
  unfold_data_at (@data_at Noise.CS sh (Tstruct I._cookie_checker noattr) _ (cc_addr wb)).
  rewrite (@field_at_data_at Noise.CS sh _ (DOT I._secret)).
  rewrite (@field_address_offset Noise.CS) by auto with field_compatible.
  unfold hbytes. rewrite HL, (@hck5_p6_tuchar_cs HCS Noise.CS).
  simpl. rewrite isptr_offset_val_zero by (destruct FCC; auto).
  apply pred_ext; cancel.
Qed.

Lemma hck5_p6_cc_fold sh a CC lk : cc_ok CC ->
  @data_at Noise.CS sh t_cc (bytes (cc_secret CC), (bytes (cc_ekey CC), (bytes (cc_mkey CC),
                             (Vlong (cc_birth CC), (lk, cc_dev CC))))) a |-- checker_rep sh a CC.
Proof. intros. unfold checker_rep. Exists lk. entailer!. Qed.

Lemma hck5_p6_cc_close sh wb CC lk : @field_compatible Noise.CS t_dev [] wb -> cc_ok CC ->
  hbytes sh (cc_secret CC) (cc_addr wb) *
  @field_at W_cookie_mac sh t_dev (DOT HK._cookie_checker DOT HK._secret_birthdate) (Vlong (cc_birth CC)) wb *
  hck5_p6_ccrest sh (cc_addr wb) CC lk |-- checker_rep sh (cc_addr wb) CC.
Proof.
  intros FC OK. erewrite <- (hck5_p6_cc_open sh wb CC lk); [| exact FC | destruct OK; auto | reflexivity].
  apply hck5_p6_cc_fold; auto.
Qed.

Lemma hck5_p6_hb_out sh l p : hbytes sh l p |-- hout sh (Zlength l) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hck5_p6_hb_at sh l p : hbytes sh l p = bytes_at sh l p.
Proof. unfold hbytes, bytes_at. apply hck5_p6_tuchar_cs. Qed.

Lemma hck5_p6_tbool_cs sh (v: val) p :
  @data_at Noise.CS sh tbool v p = @data_at W_cookie_mac sh tbool v p.
Proof. exact (f_equal (fun f => f p) (@data_at_change_composite Noise.CS W_cookie_mac _ sh tbool v v (JMeq_refl v) eq_refl)). Qed.

Lemma hck5_p6_and1 x : Int.and x (Int.repr 1) =
  if negb (Int.eq (Int.and x (Int.repr 1)) Int.zero) then Int.one else Int.zero.
Proof.
  change (Int.repr 1) with (Int.repr (two_p 1 - 1)).
  rewrite <- Int.zero_ext_and by lia.
  pose proof (Int.zero_ext_range 1 x ltac:(rep_lia)) as Hr. change (two_p 1) with 2 in Hr.
  rewrite <- (Int.repr_unsigned (Int.zero_ext 1 x)).
  assert (E: Int.unsigned (Int.zero_ext 1 x) = 0 \/ Int.unsigned (Int.zero_ext 1 x) = 1) by lia.
  destruct E as [E|E]; rewrite E; reflexivity.
Qed.

Lemma hck5_p6_shim_fold gv S rl : shim_ok S ->
  @data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
  @data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
  @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
  @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
  @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
  @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
  @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
  @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
  @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
  @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
  @data_at Noise.CS Ews tbool (Val.of_bool rl) (gv _wg_shim_ratelimit_allow)
  |-- shim_core gv (mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S)
                    (s_fails S) (s_frees S) (s_failnext S) (s_released S) rl).
Proof. intros. unfold shim_core. simpl. entailer!. Qed.

Lemma hck5_p6_hout_len sh n (l: list byte) p : Zlength l = n -> hout sh n p = hout sh (Zlength l) p.
Proof. intros; subst; auto. Qed.

Ltac hck5_p6_flat :=
  cbv beta iota delta [app hck5_bside hck5_bufs hck5_scr2 hck5_snaps0 hck5_globs hck5_lvars].

Lemma hck5_P6_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S5c x25519 gv L FR) hck5_P6
    (overridePost (hck5_S6a x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S5c, hck5_Delta, hck5_R, hck5_P6. simplify_func_tycontext. abbreviate_semax.
  Intros R S A m c Q cmode C ck MSG1 C1.
  hck5_p6_flat.
  forward_call tt. Intros b0.
  forward_if (hck5_p6_J gv L FR R S A m c Q cmode C1 MSG1).
  { apply prop_right. intros [_ X]. apply (f_equal Int.signed) in X.
    rewrite Int.signed_mone, Int.signed_repr in X by rep_lia. lia. }
  { forward_call tt. Intros i.
    forward_if (hck5_p6_J gv L FR R S A m c Q cmode C1 MSG1).
    { forward_call tt. Intros k.
      rewrite (hck5_p6_hbytes_W Ews MSG1 m).
      assert (Hi: 0 <= i < Zlength MSG1).
      { match goal with Hl: Int64.ltu _ _ = true |- _ => unfold Int64.ltu in Hl;
          rewrite !Int64.unsigned_repr in Hl by (destruct H1 as (?&?&?); rep_lia);
          destruct (zlt _ _); [lia | discriminate] end. }
      forward.
      all: match goal with |- context [@Znth val ?d ?j (bytes ?l)] =>
        replace (@Znth val d j (bytes l)) with (Vubyte (Znth j l))
          by (unfold bytes; rewrite Znth_map by lia; reflexivity) end.
      { entailer!. pose proof (Byte.unsigned_range_2 (Znth i MSG1)). lia. }
      forward.
      { entailer!. rewrite hck5_p6_mods255 by lia. split.
        - rewrite Int.signed_repr; pose proof (Z.mod_pos_bound k 255); rep_lia.
        - intros [_ X]. apply (f_equal Int.signed) in X.
          rewrite Int.signed_mone, Int.signed_repr in X by rep_lia. lia. }
      rewrite hck5_p6_mods255 by lia.
      forward.
      match goal with |- context [upd_Znth i (bytes MSG1) (Vint (Int.zero_ext 8 ?x))] =>
        rewrite (hck5_p6_zext x); unfold hck5_p6_J; hck5_p6_flat;
        Exists (upd_Znth i MSG1 (Byte.repr (Int.unsigned (Int.zero_ext 8 x)))) true end.
      entailer!.
      { rewrite Zlength_upd_Znth; auto. }
      rewrite hck5_p6_hbytes_W, Zlength_upd_Znth. unfold bytes. rewrite upd_Znth_map. cancel. }
    { forward. unfold hck5_p6_J; hck5_p6_flat. Exists MSG1 false. entailer!. }
  }
  { forward. unfold hck5_p6_J; hck5_p6_flat. Exists MSG1 false. entailer!. }
  unfold hck5_p6_J. hck5_p6_flat. Intros MSG2 corr.
  sep_apply (hck5_p6_hb_out Ews MSG1 c).
  replace (Zlength MSG1) with (Zlength MSG2) by lia.
  forward_call (Ews, c, Ews, m, MSG2).
  { entailer!. match goal with Hz: Zlength MSG2 = q_n Q |- _ => rewrite Hz end.
    destruct c; try contradiction; destruct m; try contradiction; reflexivity. }
  { destruct H1 as (?&?&_). rep_lia. }
  forward_call tt. Intros b1. forward.
  forward_call tt. Intros b2.
  unfold shim_state4, shim_core. Intros.
  rename H12 into HSok.
  rewrite (hck5_p6_tbool_cs Ews (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow)).
  forward.
  set (rl := negb (Int.eq (Int.and (Int.repr b2) (Int.repr 1)) Int.zero)).
  replace (Vint (if Int.eq (Int.and (Int.repr b2) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    with (Val.of_bool rl) by (unfold rl; destruct (Int.eq _ _); reflexivity).
  rewrite <- hck5_p6_tbool_cs.
  sep_apply (hck5_p6_shim_fold gv S rl HSok).
  set (S' := mkShim (s_boot S) (s_rsec S) (s_rnsec S) (s_log S) (s_logprev S) (s_u32 S) (s_allocs S)
                    (s_fails S) (s_frees S) (s_failnext S) (s_released S) rl).
  set (CC2 := hck5_CC2 x25519 R L (q_now Q) cmode).
  assert_PROP (@field_compatible Noise.CS t_dev [] (l_wb L)) as FCwb by (unfold hck5_drest; entailer!).
  unfold checker_rep. Intros lk. rename H12 into HCok.
  erewrite (hck5_p6_cc_open Tsh (l_wb L) CC2 lk); [| exact FCwb | destruct HCok; auto | reflexivity].
  Intros.
  forward.
  assert (HL32: Zlength (cc_secret CC2) = 32) by (destruct HCok; auto).
  rewrite (hck5_p6_hout_len Tsh 32 (cc_secret CC2) (l_secret L) HL32).
  forward_call (Tsh, l_secret L, Tsh, cc_addr (l_wb L), cc_secret CC2).
  { entailer!. rewrite HL32. unfold cc_addr, OFS_DEV_CHECKER. simpl. rewrite isptr_offset_val_zero. reflexivity.
    destruct (l_wb L); try contradiction; simpl; auto. }
  sep_apply (hck5_p6_cc_close Tsh (l_wb L) CC2 lk FCwb HCok).
  rewrite (hck5_p6_and1 (Int.repr b1)).
  set (chk := negb (Int.eq (Int.and (Int.repr b1) (Int.repr 1)) Int.zero)).
  unfold hck5_S6a.
  Exists R S' A m c Q cmode C ck. Exists MSG1 C1 MSG2 corr chk rl.
  hck5_p6_flat. unfold shim_state4.
  entailer!.
  { unfold hck5_before_val; simpl; auto. }
  apply derives_refl.
Qed.

End P6.
