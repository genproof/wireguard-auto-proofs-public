(* law config_any: helpers of hcf5_P5b_ok.
   The snapshot hq field by field (at the world W), its byte fields as HCS byte buffers. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require WgNoise.harness.x_config_any.code.
Local Open Scope logic.

Module HF := WgNoise.harness.x_config_any.code.

#[local] Instance hcf5_p5b_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.

Section W.
#[local] Existing Instance W_config_any.

(* a byte field of the snapshot at p, as an HCS buffer *)
Definition hcf5_p5b_ba (sh: share) (n: Z) (f: ident) (b: list val) (p: val) : mpred :=
  @data_at HCS sh (tarray tuchar n) b (field_address t_hsnap (DOT f) p).

Definition hcf5_p5b_flds (sh: share) (a b c d e f g h: val) (E1 E2 E3 E4 E5 E6 E7 E8: list val) (r: val)
  (p: val) : mpred :=
  field_at sh t_hsnap (DOT HF._peer) a p * field_at sh t_hsnap (DOT HF._next) b p *
  field_at sh t_hsnap (DOT HF._hashed) c p * field_at sh t_hsnap (DOT HF._type) d p *
  field_at sh t_hsnap (DOT HF._index) e p * field_at sh t_hsnap (DOT HF._state) f p *
  field_at sh t_hsnap (DOT HF._last_initiation_consumption) g p *
  field_at sh t_hsnap (DOT HF._static_identity) h p *
  hcf5_p5b_ba sh 32 HF._ephemeral_private E1 p * hcf5_p5b_ba sh 32 HF._remote_static E2 p *
  hcf5_p5b_ba sh 32 HF._remote_ephemeral E3 p * hcf5_p5b_ba sh 32 HF._precomputed_static_static E4 p *
  hcf5_p5b_ba sh 32 HF._preshared_key E5 p * hcf5_p5b_ba sh 32 HF._hash E6 p *
  hcf5_p5b_ba sh 32 HF._chaining_key E7 p * hcf5_p5b_ba sh 12 HF._latest_timestamp E8 p *
  field_at sh t_hsnap (DOT HF._remote_index) r p.

Lemma hcf5_p5b_arr sh n b x :
  @data_at HCS sh (tarray tuchar n) b x = @data_at W_config_any sh (tarray tuchar n) b x.
Proof.
  apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar n)); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p5b_split sh (a b c d e f g h: val) (E1 E2 E3 E4 E5 E6 E7 E8: list val) (r p: val) :
  data_at sh t_hsnap ((a, (b, (c, (d, (e, (f, (g, (h, (E1, (E2, (E3, (E4, (E5, (E6, (E7, (E8, r))))))))))))))))
    : reptype t_hsnap) p =
  !! field_compatible t_hsnap [] p && (hcf5_p5b_flds sh a b c d e f g h E1 E2 E3 E4 E5 E6 E7 E8 r p * spacer sh 17 20 p).
Proof.
  unfold hcf5_p5b_flds, hcf5_p5b_ba. rewrite !hcf5_p5b_arr.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_hsnap (DOT HF._ephemeral_private)),
    (field_at_data_at sh t_hsnap (DOT HF._remote_static)),
    (field_at_data_at sh t_hsnap (DOT HF._remote_ephemeral)),
    (field_at_data_at sh t_hsnap (DOT HF._precomputed_static_static)),
    (field_at_data_at sh t_hsnap (DOT HF._preshared_key)),
    (field_at_data_at sh t_hsnap (DOT HF._hash)),
    (field_at_data_at sh t_hsnap (DOT HF._chaining_key)),
    (field_at_data_at sh t_hsnap (DOT HF._latest_timestamp)).
  apply pred_ext.
  - assert_PROP (field_compatible t_hsnap [] p).
    { saturate_local. apply prop_right. destruct H as (? & ? & ? & ? & _). repeat split; auto. }
    entailer!.
  - Intros. cancel.
Qed.

(* hq before its writes *)
Definition hcf5_p5b_fa (f: ident) (p: val) : val := field_address t_hsnap (DOT f) p.

Lemma hcf5_p5b_open sh p :
  data_at_ sh t_hsnap p =
  !! field_compatible t_hsnap [] p &&
  (field_at sh t_hsnap (DOT HF._peer) Vundef p * field_at sh t_hsnap (DOT HF._next) Vundef p *
   field_at sh t_hsnap (DOT HF._hashed) Vundef p * field_at sh t_hsnap (DOT HF._type) Vundef p *
   field_at sh t_hsnap (DOT HF._index) Vundef p * field_at sh t_hsnap (DOT HF._state) Vundef p *
   field_at sh t_hsnap (DOT HF._last_initiation_consumption) Vundef p *
   field_at sh t_hsnap (DOT HF._static_identity) Vundef p *
   hout sh 32 (hcf5_p5b_fa HF._ephemeral_private p) * hout sh 32 (hcf5_p5b_fa HF._remote_static p) *
   hout sh 32 (hcf5_p5b_fa HF._remote_ephemeral p) * hout sh 32 (hcf5_p5b_fa HF._precomputed_static_static p) *
   hout sh 32 (hcf5_p5b_fa HF._preshared_key p) * hout sh 32 (hcf5_p5b_fa HF._hash p) *
   hout sh 32 (hcf5_p5b_fa HF._chaining_key p) * hout sh 12 (hcf5_p5b_fa HF._latest_timestamp p) *
   field_at sh t_hsnap (DOT HF._remote_index) Vundef p * spacer sh 17 20 p).
Proof.
  unfold data_at_.
  transitivity (data_at sh t_hsnap ((Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef, (Vundef,
    (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 32,
    (Zrepeat Vundef 32, (Zrepeat Vundef 32, (Zrepeat Vundef 12, Vundef)))))))))))))))) : reptype t_hsnap) p).
  { reflexivity. }
  rewrite hcf5_p5b_split. unfold hcf5_p5b_flds, hcf5_p5b_ba, hcf5_p5b_fa, hout. reflexivity.
Qed.

(* the snapshot at the world *)
Lemma hcf5_p5b_xW sh sn p :
  @data_at HCS sh t_hsnap (hsnap_val sn) p =
  data_at sh t_hsnap ((e_peer (sn_entry sn), (sn_next sn, (Val.of_bool (sn_hashed sn), (Vint (e_type (sn_entry sn)),
    (Vint (e_index (sn_entry sn)), (Vint (hs_state (sn_hs sn)), (Vlong (hs_lic (sn_hs sn)), (hs_sid (sn_hs sn),
    (bytes (hs_eph (sn_hs sn)), (bytes (hs_rstatic (sn_hs sn)), (bytes (hs_reph (sn_hs sn)), (bytes (hs_ss (sn_hs sn)),
    (bytes (hs_psk (sn_hs sn)), (bytes (hs_hash (sn_hs sn)), (bytes (hs_ck (sn_hs sn)), (bytes (hs_ts (sn_hs sn)),
    Vint (hs_rindex (sn_hs sn)))))))))))))))))) : reptype t_hsnap) p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite HCS W_config_any hcf5_p5b_cceH sh t_hsnap (hsnap_val sn)
    _ (@JMeq_refl _ (hsnap_val sn)) ltac:(vm_compute; reflexivity))).
Qed.

(* hq after its writes *)
Lemma hcf5_p5b_close sh p sn (a b c d e f g h r: val) (E1 E2 E3 E4 E5 E6 E7 E8: list byte) :
  a = e_peer (sn_entry sn) -> b = sn_next sn -> c = Val.of_bool (sn_hashed sn) -> d = Vint (e_type (sn_entry sn)) ->
  e = Vint (e_index (sn_entry sn)) -> f = Vint (hs_state (sn_hs sn)) -> g = Vlong (hs_lic (sn_hs sn)) ->
  h = hs_sid (sn_hs sn) -> r = Vint (hs_rindex (sn_hs sn)) ->
  E1 = hs_eph (sn_hs sn) -> E2 = hs_rstatic (sn_hs sn) -> E3 = hs_reph (sn_hs sn) -> E4 = hs_ss (sn_hs sn) ->
  E5 = hs_psk (sn_hs sn) -> E6 = hs_hash (sn_hs sn) -> E7 = hs_ck (sn_hs sn) -> E8 = hs_ts (sn_hs sn) ->
  Zlength E1 = 32 -> Zlength E2 = 32 -> Zlength E3 = 32 -> Zlength E4 = 32 -> Zlength E5 = 32 ->
  Zlength E6 = 32 -> Zlength E7 = 32 -> Zlength E8 = 12 ->
  field_compatible t_hsnap [] p ->
  field_at sh t_hsnap (DOT HF._peer) a p * field_at sh t_hsnap (DOT HF._next) b p *
  field_at sh t_hsnap (DOT HF._hashed) c p * field_at sh t_hsnap (DOT HF._type) d p *
  field_at sh t_hsnap (DOT HF._index) e p * field_at sh t_hsnap (DOT HF._state) f p *
  field_at sh t_hsnap (DOT HF._last_initiation_consumption) g p *
  field_at sh t_hsnap (DOT HF._static_identity) h p *
  hbytes sh E1 (field_address t_hsnap (DOT HF._ephemeral_private) p) * hbytes sh E2 (field_address t_hsnap (DOT HF._remote_static) p) *
  hbytes sh E3 (field_address t_hsnap (DOT HF._remote_ephemeral) p) * hbytes sh E4 (field_address t_hsnap (DOT HF._precomputed_static_static) p) *
  hbytes sh E5 (field_address t_hsnap (DOT HF._preshared_key) p) * hbytes sh E6 (field_address t_hsnap (DOT HF._hash) p) *
  hbytes sh E7 (field_address t_hsnap (DOT HF._chaining_key) p) * hbytes sh E8 (field_address t_hsnap (DOT HF._latest_timestamp) p) *
  field_at sh t_hsnap (DOT HF._remote_index) r p * spacer sh 17 20 p
  |-- @data_at HCS sh t_hsnap (hsnap_val sn) p.
Proof.
  intros -> -> -> -> -> -> -> -> -> Q1 Q2 Q3 Q4 Q5 Q6 Q7 Q8 L1 L2 L3 L4 L5 L6 L7 L8 FC.
  rewrite hcf5_p5b_xW, hcf5_p5b_split.
  unfold hcf5_p5b_flds, hcf5_p5b_ba, hbytes.
  rewrite L1, L2, L3, L4, L5, L6, L7, L8.
  subst E1 E2 E3 E4 E5 E6 E7 E8.
  apply andp_right; [apply prop_right; exact FC | apply derives_refl].
Qed.

End W.
