(* law keypairs: segment L0 of the loop body (op = nondet_u8() % 8; the clock moves). *)
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
Require Import WgNoise.proof.harness.keypairs.hkp5_defs.

#[local] Existing Instance W_keypairs.
Local Open Scope logic.

Lemma hkp5_segL0_mods u m : 0 <= u <= Byte.max_unsigned -> 0 < m <= 64 ->
  Int.mods (Int.repr u) (Int.repr m) = Int.repr (u mod m).
Proof.
  intros Hu Hm. unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma hkp5_segL0_now now dd : Int64.unsigned now < 2 ^ 62 ->
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

Lemma hkp5_segL0_tulong_cs {cs1 cs2: compspecs} sh v p :
  @data_at cs1 sh tulong v p = @data_at cs2 sh tulong v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext.
  unfold field_compatible; simpl.
  split; intros (?&?&?&?&?); (repeat split); auto;
    destruct p; try contradiction; unfold align_compatible in *;
    (apply align_compatible_rec_by_value with Mint64; [reflexivity|]);
    apply (align_compatible_rec_by_value_inv _ _ Mint64) in H2; auto.
Qed.

Lemma hkp5_segL0_ok {Espec: OracleKind} x25519 (F: hkp5_fix) V steps FR i R :
  semax (hkp5_Delta hkp5_G_L0) (hkp5_Icont x25519 F V steps FR i) hkp5_segL0
    (overridePost (EX op: Z, hkp5_PL0 x25519 F V steps FR i op) R).
Proof.
  unfold hkp5_Icont, hkp5_St, hkp5_Delta, hkp5_segL0.
  Intros Y.
  destruct F as [gv w t pt p raw pub snap opub first second].
  destruct Y as [S ww kc P KS T HH now next_id id_known hsn].
  pose proof H1 as Hinv.
  destruct H1 as (_ & _ & _ & _ & _ & _ & _ & _ & Hnow & _).
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn] in Hnow |- *.
  abbreviate_semax.
  forward_call tt. Intros u.
  forward.
  { entailer!. match goal with Hc: _ /\ Int.repr 8 = Int.mone |- _ => apply proj2 in Hc;
      apply (f_equal Int.unsigned) in Hc; rewrite Int.unsigned_repr in Hc by rep_lia; discriminate end. }
  rewrite hkp5_segL0_mods by lia.
  forward_call tt. Intros d0.
  forward_call tt. Intros u2.
  forward.
  { entailer!. rewrite hkp5_segL0_mods by lia. rewrite Int.unsigned_repr by (pose proof (Z.mod_pos_bound u2 64); rep_lia).
    split; [pose proof (Z.mod_pos_bound u2 64); change (Int.unsigned Int64.iwordsize') with 64; lia |].
    intros [_ Hc]. apply (f_equal Int.unsigned) in Hc. rewrite Int.unsigned_repr in Hc by rep_lia. discriminate. }
  set (dd := Int64.shru d0 _).
  set (now' := if Int64.ltu dd (Int64.sub (Int64.shl Int64.one (Int64.repr 62)) now) then Int64.add now dd else now).
  forward_if (temp KC._now (Vlong now')).
  { forward. entailer!. unfold now', Int64.ltu. rewrite zlt_true by assumption. reflexivity. }
  { forward. entailer!. unfold now', Int64.ltu. rewrite zlt_false by assumption. reflexivity. }
  assert (Hnow': Int64.unsigned now' < 2 ^ 62) by (apply hkp5_segL0_now; exact Hnow).
  clearbody now' dd.
  unfold shim_state4 at 1, shim_core at 1. Intros. rename H4 into HSok.
  rewrite (@hkp5_segL0_tulong_cs Noise.CS W_keypairs _ _ (gv _wg_shim_boottime_ns)).
  change _wg_shim_boottime_ns with KC._wg_shim_boottime_ns. forward.
  rewrite (@hkp5_segL0_tulong_cs W_keypairs Noise.CS _ _ (gv KC._wg_shim_boottime_ns)).
  change KC._wg_shim_boottime_ns with _wg_shim_boottime_ns.
  set (Y' := mkKY5 (shim_set_boot S now') ww kc P KS T HH now' next_id id_known hsn).
  assert (Hinv': hkp5_inv {| f_gv := gv; f_w := w; f_t := t; f_pt := pt; f_p := p; f_raw := raw; f_pub := pub;
    f_snap := snap; f_opub := opub; f_first := first; f_second := second |} V Y').
  { destruct Hinv as (I1&I2&I3&I4&I5&I6&I7&I8&_&I10).
    exact (conj I1 (conj I2 (conj I3 (conj I4 (conj I5 (conj I6 (conj I7 (conj I8 (conj Hnow' I10))))))))). }
  destruct R as [Rn Rb Rc Rr]. cbn [overridePost RA_normal].
  Exists (u mod 8). unfold hkp5_PL0. Exists Y'.
  unfold hkp5_SEP, hkp5_world, hk5_items, hkp5_hglobs, hkp5_globs, hkp5_temps, hkp5_lvars, Y'.
  cbn [app f_gv f_w f_t f_pt f_p f_raw f_pub f_snap f_opub f_first f_second y_S y_w y_kc y_P y_KS y_T y_H y_now
       y_next_id y_id_known y_hsn].
  fold Y'.
  unfold shim_state4, shim_core.
  cbn [shim_set_boot s_boot s_rsec s_rnsec s_log s_logprev s_u32 s_allocs s_fails s_frees s_failnext s_released
       s_rlallow].
  entailer!.
  apply Z.mod_pos_bound; lia.
Qed.
