(* law replay: the loop body, segment L2a (d = draw_u64() >> (nondet_u8() % 64); now += d if it stays
   below 2^62; wg_shim_boottime_ns = now; hs_take(&snap, &pa.handshake); ret = consume_initiation(m, &wb)).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.harness.common.hc_prog3.
Require Import WgNoise.proof.harness.replay.hrp3_spec.
Require Import WgNoise.proof.harness.replay.hrp3_model.
Require Import WgNoise.proof.harness.replay.hrp3_defs.
Require WgNoise.contracts.x_replay.
Require WgNoise.harness.x_replay.code.

#[local] Existing Instance W_replay.
Local Open Scope Z_scope.

Lemma hrp3_segL2a_mods u : 0 <= u <= Byte.max_unsigned ->
  Int.mods (Int.repr u) (Int.repr 64) = Int.repr (u mod 64).
Proof.
  intros Hu. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma hrp3_segL2a_now now dd : Int64.unsigned now < 2 ^ 62 ->
  Int64.unsigned (if Int64.ltu dd (Int64.sub (Int64.shl Int64.one (Int64.repr 62)) now)
                  then Int64.add now dd else now) < 2 ^ 62.
Proof.
  intros Hn. pose proof (Int64.unsigned_range now) as Rn. pose proof (Int64.unsigned_range dd) as Rd.
  assert (E: Int64.unsigned (Int64.sub (Int64.shl Int64.one (Int64.repr 62)) now) = 2 ^ 62 - Int64.unsigned now).
  { change (Int64.shl Int64.one (Int64.repr 62)) with (Int64.repr (2 ^ 62)). unfold Int64.sub.
    rewrite (Int64.unsigned_repr (2 ^ 62)) by rep_lia. rewrite Int64.unsigned_repr by rep_lia. reflexivity. }
  unfold Int64.ltu. rewrite E. destruct (zlt (Int64.unsigned dd) (2 ^ 62 - Int64.unsigned now)); [| lia].
  unfold Int64.add. rewrite Int64.unsigned_repr by rep_lia. lia.
Qed.

Lemma hrp3_segL2a_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hrp3_segL2a_shim_fold gv S : shim_ok S ->
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
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
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) * refwarn gv)%logic
  |-- shim_state gv S.
Proof. intros H. unfold shim_state. apply andp_right; [apply prop_right; exact H | apply derives_refl]. Qed.

Lemma hrp3_segL2a_peers sh p P : peer_rep sh p P |-- peers_rep [(p, sh, P)].
Proof. unfold peers_rep. simpl. cancel. Qed.

Lemma hrp3_segL2a_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) V sp ap mp steps i R :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec)
    (hrp3_PL1 x25519 aead_dec F V sp ap mp steps FR i) hrp3_segL2a
    (overridePost (hrp3_PL2a x25519 aead_dec F V sp ap mp steps FR i)
       (loop1_ret_assert (hrp3_Icont x25519 aead_dec F V sp ap mp steps FR i) R)).
Proof.
  intros HF HX HA.
  destruct F as [gv wa wb ita itb pta ptb pa pb ia ib rawa rawb psk ssb latest ci snap].
  unfold hrp3_PL1, hrp3_Delta, hrp3_lvars, hrp3_temps, hrp3_segL2a. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  Intros Y M kind.
  destruct Y as [S TA PB PA lat last now hs Ms ha Ma].
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma] in *.
  pose proof H1 as Hinv. destruct H1 as (_ & _ & _ & Hpa & Hlat & Hlast & Hnow & _).
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma f_pb f_wa f_pa] in *.
  unfold hrp3_world, hrp3_globs, app. cbn [f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  abbreviate_semax.
  forward_call tt. Intros d0.
  forward_call tt. Intros u.
  set (F0 := {| f_gv := gv; f_wa := wa; f_wb := wb; f_ita := ita; f_itb := itb; f_pta := pta; f_ptb := ptb;
    f_pa := pa; f_pb := pb; f_ia := ia; f_ib := ib; f_rawa := rawa; f_rawb := rawb; f_psk := psk; f_ssb := ssb;
    f_latest := latest; f_ci := ci; f_snap := snap |}) in *.
  forward.
  { entailer!. rewrite hrp3_segL2a_mods by lia. rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound u 64); rep_lia).
    split; [pose proof (Z.mod_pos_bound u 64); change (Int.unsigned Int64.iwordsize') with 64; lia |].
    intros [_ Hc]. apply (f_equal Int.unsigned) in Hc. rewrite Int.unsigned_repr in Hc by rep_lia. discriminate. }
  set (dd := Int64.shru d0 _).
  set (now' := if Int64.ltu dd (Int64.sub (Int64.shl Int64.one (Int64.repr 62)) now) then Int64.add now dd else now).
  forward_if (temp RC._now (Vlong now')).
  { forward. entailer!. unfold now', Int64.ltu. rewrite zlt_true by exact H5. reflexivity. }
  { forward. entailer!. unfold now', Int64.ltu. rewrite zlt_false by exact H5. reflexivity. }
  assert (Hnow': Int64.unsigned now' < 2 ^ 62) by (apply hrp3_segL2a_now; exact Hnow).
  clearbody now' dd.
  unfold shim_state at 1. Intros. rename H5 into HSok.
  rewrite (@hrp3_segL2a_tulong_cs Noise.CS W_replay _ _ (gv _wg_shim_boottime_ns)).
  change _wg_shim_boottime_ns with RC._wg_shim_boottime_ns. forward.
  rewrite (@hrp3_segL2a_tulong_cs W_replay Noise.CS _ _ (gv RC._wg_shim_boottime_ns)).
  change RC._wg_shim_boottime_ns with _wg_shim_boottime_ns.
  sep_apply (hrp3_segL2a_shim_fold gv (shim_set_boot S now') HSok).
  assert_PROP (isptr pa /\ isptr wb) as Hpw by entailer!.
  forward_call (Tsh, snap, Tsh, pa, PA, Tsh, itb, hrp3_TB0 pa, hrp3_E0 pa).
  { split; [unfold t_entry, hrp3_TB0, t_add; cbn [t_D sfind]; rewrite if_true by reflexivity; reflexivity |].
    destruct Hpw as [Hpp Hwp]. split; [destruct pa; try contradiction; discriminate |].
    destruct Hpa as (?&?&?&?&?&->). destruct wb; try contradiction; discriminate. }
  assert (Hnx: p_pknext PA = nullval) by (destruct Hpa as (?&?&?&?&?&->); reflexivity).
  assert (Hlic: hs_lic (p_hs PA) = last) by (destruct Hpa as (?&?&?&?&?&->); reflexivity).
  assert (HPA1: p_refs PA = Int.one) by (destruct Hpa as (?&?&?&?&?&->); reflexivity).
  change (hrp3_mbuf true M mp) with (@malloc_token W_replay Ews t_init mp * init_rep Ews mp M)%logic.
  Intros.
  sep_apply (hrp3_segL2a_peers Tsh pa PA).
  change (ptable Tsh ptb pa) with (ptable Tsh (d_ptab (hrp3_DB x25519 F0 V)) pa).
  forward_call (gv, shim_set_boot S now', v_kc V, Ews, mp, M, Tsh, wb, hrp3_DB x25519 F0 V, Tsh, pa, [(pa, Tsh, PA)]).
  { split3; [constructor; auto | split; auto |].
    split.
    - constructor; [| constructor]. rewrite Hlic. rewrite Int64.signed_eq_unsigned; [rep_lia |].
      unfold Int64.max_signed, Int64.half_modulus, Int64.modulus, Int64.wordsize, Wordsize_64.wordsize. simpl. lia.
    - (* A's peer at B holds one reference (peers_refs_ok) *)
      constructor; [| constructor]. rewrite HPA1. rewrite Int.unsigned_one. lia. }
  forward.
  set (Y' := mkRDyn (shim_set_boot S now') TA PB PA lat last now' hs Ms ha Ma).
  assert (Hinv': hrp3_inv x25519 aead_dec F0 V Y').
  { destruct Hinv as (?&?&?&?&?&?&?&?). unfold Y'. repeat split; auto. }
  destruct R as [Rn Rb Rc Rr]. cbn [loop1_ret_assert RA_normal].
  unfold hrp3_PL2a. Exists Y' M kind.
  unfold hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars, app. unfold Y'.
  cbn [y_S y_TA y_PB y_PA y_latest y_last y_now y_hs y_Ms y_ha y_Ma f_gv f_wa f_wb f_ita f_itb f_pta f_ptb f_pa f_pb
       f_ia f_ib f_rawa f_rawb f_psk f_ssb f_latest f_ci f_snap].
  fold F0. fold Y'.
  change (hrp3_mbuf true M mp) with (@malloc_token W_replay Ews t_init mp * init_rep Ews mp M)%logic.
  entailer!.
  change (d_ptab (hrp3_DB x25519 F0 V)) with ptb. change (f_wa F0) with wa. change (f_wb F0) with wb.
  change (f_ita F0) with ita. change (f_itb F0) with itb. change (f_pta F0) with pta. change (f_ptb F0) with ptb.
  change (f_pa F0) with pa. change (f_pb F0) with pb. change (f_rawa F0) with rawa. change (f_rawb F0) with rawb.
  change (f_psk F0) with psk. change (f_ssb F0) with ssb. change (f_latest F0) with latest. change (f_gv F0) with gv.
  cancel.
Qed.
