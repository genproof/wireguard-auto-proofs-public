(* law replay: main's segment F (statements 24..27, after the loop: the three frees, return 0 with the locals
   back to data_at_ (hrp3_close)).
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

#[local] Instance hrp3_segF_CCE1 : change_composite_env HCS W_replay.
Proof. make_cs_preserve HCS W_replay. Defined.
#[local] Instance hrp3_segF_CCE2 : change_composite_env W_replay Noise.CS.
Proof. make_cs_preserve W_replay Noise.CS. Defined.

Lemma hrp3_segF_mid (v: reptype t_mident) (p: val) :
  @data_at HCS Tsh t_mident v p |-- @data_at_ W_replay Tsh (Tstruct RC._m_identity noattr) p.
Proof.
  sep_apply (@data_at_data_at_ HCS). rewrite (@data_at__change_composite HCS W_replay _ Tsh t_mident) by reflexivity.
  apply derives_refl.
Qed.

Lemma hrp3_segF_mcinit (p: val) :
  @data_at_ HCS Tsh t_mcinit p |-- @data_at_ W_replay Tsh (Tstruct RC._m_consumed_initiation noattr) p.
Proof.
  rewrite (@data_at__change_composite HCS W_replay _ Tsh t_mcinit) by reflexivity. apply derives_refl.
Qed.

Lemma hrp3_segF_hsnap (p: val) :
  @data_at_ HCS Tsh t_hsnap p |-- @data_at_ W_replay Tsh (Tstruct RC._hs_snap noattr) p.
Proof.
  rewrite (@data_at__change_composite HCS W_replay _ Tsh t_hsnap) by reflexivity. apply derives_refl.
Qed.

Lemma hrp3_segF_hbytes (bs: list byte) (n: Z) (p: val) :
  Zlength bs = n ->
  hbytes Tsh bs p |-- @data_at_ W_replay Tsh (tarray tuchar n) p.
Proof.
  intros <-. unfold hbytes. sep_apply (@data_at_data_at_ HCS).
  rewrite (@data_at__change_composite HCS W_replay _ Tsh (tarray tuchar (Zlength bs))) by reflexivity.
  apply derives_refl.
Qed.

Lemma hrp3_segF_mbuf (b: bool) (M: init_msg) (p: val) :
  hrp3_mbuf b M p |--
  (if eq_dec p nullval then emp else (@malloc_token W_replay Ews t_init p * @data_at_ W_replay Ews t_init p))%logic.
Proof.
  unfold hrp3_mbuf. sep_apply (@malloc_token_local_facts W_replay). Intros.
  destruct (eq_dec p nullval) as [->|Hp].
  { match goal with H: malloc_compatible _ _ |- _ => unfold malloc_compatible, nullval in H; simpl in H; contradiction end. }
  rewrite (@data_at__change_composite W_replay Noise.CS _ Ews t_init) by reflexivity.
  destruct b; [| cancel].
  unfold init_rep. Intros. sep_apply (@data_at_data_at_ Noise.CS). cancel.
Qed.

Lemma hrp3_segF_ok {Espec: OracleKind} x25519 aead_enc aead_dec (F: hrp3_fix) (FR: mpred) V sp ap mp steps :
  hrp3_facts -> x25519_props x25519 -> aead_props aead_enc aead_dec ->
  semax (hrp3_Delta x25519 aead_enc aead_dec) (hrp3_Inv x25519 aead_dec F V sp ap mp steps FR) hrp3_segF
    (overridePost FF (hrp3_R (f_gv F))).
Proof.
  intros HH Hx Ha. unfold hrp3_Inv, hrp3_Delta, hrp3_R. apply hrp3_post_canon. abbreviate_semax.
  Intros i Y. unfold hrp3_St, hrp3_world, hrp3_globs, hrp3_temps, hrp3_lvars; cbn [app].
  Intros.
  unfold hrp3_segF.
  sep_apply (hrp3_segF_mbuf (y_hs Y) (y_Ms Y) sp).
  sep_apply (hrp3_segF_mbuf (y_ha Y) (y_Ma Y) ap).
  sep_apply (hrp3_segF_mbuf false (y_Ma Y) mp).
  forward_call (t_init, sp, f_gv F).
  forward_call (t_init, ap, f_gv F).
  forward_call (t_init, mp, f_gv F).
  forward.
  destruct HH as (_ & _ & Hc).
  destruct H0 as (Hra & Hrb & Hps & _ & _ & _).
  destruct H1 as (Hta & _ & _ & _ & Hlat & _).
  assert (Hss: Zlength (hrp3_SS x25519 V) = 32).
  { unfold hrp3_SS, m_precomputed_model. match goal with |- context [if ?b then _ else _] => destruct b end; [apply Hx | reflexivity]. }
  sep_apply (Hc F (hrp3_DA x25519 F V) (hrp3_DB x25519 F V) (y_TA Y) (y_PB Y) (y_PA Y) Hta).
  sep_apply (hrp3_segF_mid (mident_val (hrp3_IA x25519 V)) (f_ia F)).
  sep_apply (hrp3_segF_mid (mident_val (hrp3_IB x25519 V)) (f_ib F)).
  sep_apply (hrp3_segF_hbytes (v_RAWA V) 32 (f_rawa F) Hra).
  sep_apply (hrp3_segF_hbytes (v_RAWB V) 32 (f_rawb F) Hrb).
  sep_apply (hrp3_segF_hbytes (v_PSK V) 32 (f_psk F) Hps).
  sep_apply (hrp3_segF_hbytes (hrp3_SS x25519 V) 32 (f_ssb F) Hss).
  sep_apply (hrp3_segF_hbytes (y_latest Y) 12 (f_latest F) Hlat).
  sep_apply (hrp3_segF_mcinit (f_ci F)).
  sep_apply (hrp3_segF_hsnap (f_snap F)).
  cancel.
Qed.
