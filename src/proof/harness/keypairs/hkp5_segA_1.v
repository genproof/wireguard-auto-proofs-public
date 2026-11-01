(* law keypairs, prologue A, piece 1: statements 0..14 (globals, m_warn, now, wg_noise_init, raw, pub, setup_device, setup_peer, peer_randomize_rest).
   States: hkp5_segA_defs.v. "Prologue A".
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.keypairs.hkp5_op1.
Require Import WgNoise.proof.harness.keypairs.hkp5_spec.
Require Import WgNoise.proof.harness.keypairs.hkp5_segA_defs.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.libc.libc_bytes.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

#[local] Instance hkp5A_1_cceN : change_composite_env Noise.CS W_keypairs.
Proof. make_cs_preserve Noise.CS W_keypairs. Defined.
#[local] Instance hkp5A_1_cceH : change_composite_env HCS W_keypairs.
Proof. make_cs_preserve HCS W_keypairs. Defined.
#[local] Instance hkp5A_1_cceK : change_composite_env CKS W_keypairs.
Proof. make_cs_preserve CKS W_keypairs. Defined.

Lemma hkp5A_1_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_keypairs sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_keypairs _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hkp5A_1_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hkp5A_1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_keypairs Ews tulong (Vlong (s_boot S)) (gv KC._wg_shim_boottime_ns) *
     hkp5A_1_rest gv S))%logic.
Proof.
  unfold shim_core, hkp5A_1_rest. rewrite <- hkp5A_1_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the shim after the boot clock store *)
Definition hkp5A_1_S1 (v: int64) : shim :=
  mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

Lemma hkp5A_1_conv_dev sh v :
  @data_at_ W_keypairs sh (Tstruct KC._wg_device noattr) v = @data_at_ Noise.CS sh t_dev v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_keypairs _ sh t_dev eq_refl) v). Qed.
Lemma hkp5A_1_conv_itab sh v :
  @data_at_ W_keypairs sh (Tstruct KC._index_hashtable noattr) v = @data_at_ Noise.CS sh t_itab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_keypairs _ sh t_itab eq_refl) v). Qed.
Lemma hkp5A_1_conv_ptab sh v :
  @data_at_ W_keypairs sh (Tstruct KC._pubkey_hashtable noattr) v = @data_at_ Noise.CS sh t_ptab v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_keypairs _ sh t_ptab eq_refl) v). Qed.
Lemma hkp5A_1_conv_peer sh v :
  @data_at_ W_keypairs sh (Tstruct KC._wg_peer noattr) v = @data_at_ Noise.CS sh t_peer v.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_keypairs _ sh t_peer eq_refl) v). Qed.
Lemma hkp5A_1_conv_hsnap sh v :
  @data_at_ W_keypairs sh (Tstruct KC._hs_snap noattr) v = @data_at_ HCS sh t_hsnap v.
Proof. symmetry. exact (equal_f (@data_at__change_composite HCS W_keypairs _ sh t_hsnap eq_refl) v). Qed.
Lemma hkp5A_1_conv_bytes sh n v :
  @data_at_ W_keypairs sh (tarray tuchar n) v = hout sh n v.
Proof. unfold hout. apply data_at__tarray_tuchar_cs. Qed.

(* nondet_bytes's result as hbytes *)
Lemma hkp5A_1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_keypairs sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_keypairs _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Lemma hkp5A_1_inv x25519 F D PUB dead lsh valid birth ck sent mac1 :
  isptr (f_p F) ->
  hkp5A_inv F (p_rest_randomized (setup_peer_val x25519 D (f_w F) (f_p F) nullval PUB zeros32 (Int64.repr 1))
                 dead lsh valid birth ck sent mac1) [] [] [] (hkp5A_T1 (f_p F)) (f_p F).
Proof.
  intros Hp. unfold hkp5A_inv. cbn.
  rewrite if_true by reflexivity.
  repeat split; auto; try constructor; try (constructor; [intros []|constructor]).
  all: try (intros []); try constructor.
  all: try reflexivity; try (left; reflexivity).
Qed.

Lemma hkp5A_1_ok {Espec: OracleKind} x25519 (F: hkp5_fix) (FR: mpred) R :
  x25519_props x25519 ->
  semax (hkp5_Delta (hkp5_G_A x25519)) (hkp5_P0 F FR) hkp5A_s1 (overridePost (hkp5A_S2 x25519 F FR) R).
Proof.
  intros HX.
  destruct F as [gv w t pt p raw pub snap opub first second].
  unfold hkp5_P0, hkp5_Delta, hkp5A_s1, hkp5_lvars. cbn [f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second].
  destruct R as [RN RB RC RR].
  unfold overridePost.
  abbreviate_semax.
  forward. forward. forward. forward. forward. forward. forward. forward. forward.
  freeze FZ := - (data_at_ Ews (tarray tulong 5) (gv KC._m_warn)).
  forward_for_simple_bound 5 (EX i: Z,
    PROP () LOCAL (temp KC._id_known (Vint Int.zero); temp KC._next_id (Vlong Int64.zero);
      lvar KC._w (Tstruct KC._wg_device noattr) w;
   lvar KC._t (Tstruct KC._index_hashtable noattr) t;
   lvar KC._pt (Tstruct KC._pubkey_hashtable noattr) pt;
   lvar KC._p (Tstruct KC._wg_peer noattr) p;
   lvar KC._raw (tarray tuchar 32) raw; lvar KC._pub (tarray tuchar 32) pub;
   lvar KC._snap (Tstruct KC._hs_snap noattr) snap;
   lvar KC._opub (tarray tuchar 32) opub;
   lvar KC._first (tarray tuchar 32) first;
   lvar KC._second (tarray tuchar 32) second; gvars gv)
    SEP (FRZL FZ; data_at Ews (tarray tulong 5) (Zrepeat (Vlong Int64.zero) i ++ Zrepeat Vundef (5 - i)) (gv KC._m_warn))).
  - entailer!.
  - forward. entailer!. apply derives_refl'. f_equal. list_solve.
  - thaw FZ.
  forward.
  forward_call tt. Intros now.
  unfold shim_state4. rewrite (hkp5A_1_core_open gv hkp5_S0). Intros.
  forward.
  gather_SEP 22 23 24. replace_SEP 0 (shim_state4 gv (hkp5A_1_S1 now) (Zrepeat Int64.zero 5)).
  1: unfold shim_state4; rewrite hkp5A_1_core_open; entailer!; apply derives_refl.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  forward_call (raw, 32, Tsh). Intros bsR.
  forward_call (pub, 32, Tsh). Intros bsP.
  rewrite (hkp5A_1_nd Tsh 32 bsR) by tauto. rewrite (hkp5A_1_nd Tsh 32 bsP) by tauto.
  rewrite hkp5A_1_conv_dev, hkp5A_1_conv_itab, hkp5A_1_conv_ptab.
  forward_call (gv, hkp5A_1_S1 now, Zrepeat Int64.zero 5, Tsh, w, t, pt, Tsh, raw, map Byte.repr bsR).
  { rewrite Zlength_map; tauto. }
  Intros sec.
  set (RAW := map Byte.repr bsR). set (PUB := map Byte.repr bsP).
  change (s_boot (hkp5A_1_S1 now)) with now.
  set (D := setup_dev x25519 w t pt RAW sec now).
  change (ptable Tsh pt nullval) with (ptable Tsh (d_ptab D) nullval).
  rewrite hkp5A_1_conv_peer.
  forward_call (gv, Tsh, p, Tsh, w, D, nullval, Tsh, pub, PUB, nullval, zeros32, Int64.repr 1).
  { rewrite if_true by reflexivity. rewrite emp_sepcon. cancel. }
  { repeat split; auto; try (unfold PUB; rewrite Zlength_map; auto); try (intro; congruence). }
  rewrite !if_true by reflexivity.
  set (P0 := setup_peer_val x25519 D w p nullval PUB zeros32 (Int64.repr 1)).
  forward_call (Tsh, p, P0).
  Intros vret. destruct vret as [[[[[[dead lsh] valid] birth] ck] sent] mac1]. simpl fst in *; simpl snd in *.
  pose proof (proj1 (proj2 (proj2 (proj2 (proj2 prot_rep_lemmas3))))) as Tadd.
  sep_apply (Tadd Tsh t (mkT [] []) (hs_addr p) Tsh (mkEntry p IDX_HANDSHAKE Int.zero) writable_share_top).
  clear Tadd.
  change (d_ptab D) with pt.
  rewrite hkp5A_1_conv_hsnap, !hkp5A_1_conv_bytes.
  replace (Zrepeat (Vlong Int64.zero) 5 ++ Zrepeat Vundef (5 - 5)) with (map Vlong (Zrepeat Int64.zero 5)) by reflexivity.
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  assert (HRUN: hkp5A_run_ok (mkRA5 RAW PUB sec now)).
  { unfold hkp5A_run_ok; cbn. unfold RAW, PUB. rewrite !Zlength_map. repeat split; auto; lia. }
  unfold hkp5A_S2.
  Exists (mkRA5 RAW PUB sec now) (p_rest_randomized P0 dead lsh valid birth ck sent mac1)
    (shim_draw (hkp5A_1_S1 now) sec) (Zrepeat Int64.zero 5) (@nil hnode4) (@nil (val*share*peer)) (hkp5A_T1 p) p.
  unfold hkp5A_world, hk5_items, hkp5A_snaps0, hkp5A_oth, hkp5A_globs, hkp5A_temps, hkp5_lvars, hkp5A_H0,
    hkp5A_D, hkp5A_nhead, hk5_warr;
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second a_RAW a_PUB a_sec a_boot h5_ML h5_sp
       h5_sc h5_sn h5_frees h5_warn hk5_head hk5_mklist hnodes_rep4].
  change (peers_rep []) with (@emp mpred _ _). fold D.
  go_lower.
  pose proof (hkp5A_1_inv x25519 (mkKF5 gv w t pt p raw pub snap opub first second) D PUB dead lsh valid birth ck
                sent mac1 Pp) as HINV.
  apply andp_right; [apply prop_right; split; [exact HRUN | split; [reflexivity | split; [exact HINV | repeat split; auto]]] |].
  rewrite prop_true_andp by reflexivity. rewrite prop_true_andp by reflexivity.
  cancel.
Qed.
