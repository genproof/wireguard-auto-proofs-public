(* group noise_mix: the body of noise.c's mix_dh against its specification
   (prot_specs4.v) in the context Gprot4 (prot_prog4.v), for ANY primitive models with their properties. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot_prog4.
Require WgNoise.proof.libc.libc_bytes WgNoise.proof.blake2s.spec.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Lemma prot4_noise_mix_mix_dh_b2s sh bs p : Zlength bs <> 0 ->
  bytes_at sh bs p = WgNoise.proof.blake2s.spec.b2s_bytes sh bs p.
Proof.
  intros. unfold bytes_at, bytes. rewrite WgNoise.proof.blake2s.spec.b2s_bytes_nonempty by auto.
  apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma prot4_noise_mix_mix_dh_forget sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p |-- @data_at_ Noise.CS sh (tarray tuchar 32) p.
Proof.
  intros. unfold bytes_at, bytes. rewrite H. apply data_at_data_at_.
Qed.

Lemma prot4_noise_mix_mix_dh_bytes32 sh bs p : Zlength bs = 32 ->
  bytes_at sh bs p = @data_at Noise.CS sh (tarray tuchar 32) (map Vubyte bs) p.
Proof.
  intros. unfold bytes_at, bytes. rewrite H. reflexivity.
Qed.

Section Body.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.

Lemma prot4_noise_mix_body_mix_dh :
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot4 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_mix_dh (mix_dh_spec x25519).
Proof.
intros Hx _ _.
start_function.
unfold wg_consts; Intros.
unfold bytes_at, bytes. rewrite H0, H1.
forward_call (Tsh, v_dh_calculation, shv, pv, priv, shb, pb, pub, gv).
pose proof (Hx priv pub) as HX.
unfold dh_ok.
destruct (memneq_bool (x25519 priv pub) zeros32) eqn:Hm.
- forward_if.
  { exfalso; apply Int.one_not_zero; assumption. }
  replace_SEP 0 (WgNoise.proof.blake2s.spec.b2s_bytes Tsh (x25519 priv pub) v_dh_calculation).
  { rewrite <- prot4_noise_mix_mix_dh_b2s by lia. unfold bytes_at, bytes. rewrite HX. entailer!. }
  fold (bytes_at shc ck ckp).
  forward_call (gv, true, ckp, kp, nullval, 32, 0, shc, shk, shk, Tsh, v_dh_calculation, x25519 priv pub, shc, ckp, ck).
  { apply prop_right; simpl; rewrite HX; reflexivity. }
  { unfold wg_consts. cancel. destruct (eq_dec kp nullval); [cancel|].
    destruct (eq_dec nullval nullval) as [_|NN]; [|congruence]. cancel. }
  rewrite <- (prot4_noise_mix_mix_dh_b2s Tsh (x25519 priv pub) v_dh_calculation) by lia.
  sep_apply (prot4_noise_mix_mix_dh_forget Tsh (x25519 priv pub) v_dh_calculation HX).
  forward_call (Tsh, v_dh_calculation, 32).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_dh_calculation).
  forward.
  unfold dh_ok; rewrite Hm.
  rewrite (prot4_noise_mix_mix_dh_bytes32 shv priv pv H0), (prot4_noise_mix_mix_dh_bytes32 shb pub pb H1).
  destruct (eq_dec kp nullval) as [E|NE].
  + unfold wg_consts. entailer!.
  + destruct (eq_dec nullval nullval) as [_|NN]; [|congruence].
    unfold wg_consts. entailer!.
- forward_if.
  2: { exfalso; apply H2; reflexivity. }
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte (x25519 priv pub)) v_dh_calculation).
  unfold dh_ok; rewrite Hm.
  rewrite (prot4_noise_mix_mix_dh_bytes32 shv priv pv H0), (prot4_noise_mix_mix_dh_bytes32 shb pub pb H1).
  unfold wg_consts. entailer!.
Qed.

End Body.
