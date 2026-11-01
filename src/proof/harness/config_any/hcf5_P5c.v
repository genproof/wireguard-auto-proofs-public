(* law config_any: main's phase P5c, statements 75..84: q's cookie ANY, wg_cookie_init(&q.latest_cookie), CHECK(the cookie is zero), CHECK(hs_same(&hq, &q.handshake)).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

#[local] Instance hcf5_p5c_cce : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.
#[local] Instance hcf5_p5c_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

Lemma hcf5_p5c_fa t p gfs : field_compatible t gfs p ->
  field_address t gfs p = offset_val (nested_field_offset t gfs) p.
Proof. intros. unfold field_address. rewrite if_true by auto. reflexivity. Qed.

(* the cookie's lock and padding (never touched) *)
Definition hcf5_p5c_ckr (sh: share) (q: val) (lk: val) : mpred :=
  (field_at sh t_cookie [StructField I._lock] lk (cookie_addr q) * spacer sh 106 108 (cookie_addr q))%logic.

Ltac hcf5_p5c_sc sh f v q :=
  let E := fresh "E" in
  assert (E: cookie_addr q = field_address t_peer [StructField I._latest_cookie] q)
    by (rewrite hcf5_p5c_fa by auto with field_compatible; reflexivity);
  let X := fresh "X" in
  pose proof (field_at_app sh t_peer [StructField f] [StructField I._latest_cookie] v v q (JMeq_refl v)) as X;
  simpl app in X; change (nested_field_type t_peer [StructField I._latest_cookie]) with t_cookie in X;
  rewrite <- E in X; rewrite <- X; clear X E.

Ltac hcf5_p5c_arr sh f v q :=
  let E := fresh "E" in
  assert (E: cookie_addr q = field_address t_peer [StructField I._latest_cookie] q)
    by (rewrite hcf5_p5c_fa by auto with field_compatible; reflexivity);
  let X := fresh "X" in
  pose proof (field_at_app sh t_peer [StructField f] [StructField I._latest_cookie] v v q (JMeq_refl v)) as X;
  simpl app in X; change (nested_field_type t_peer [StructField I._latest_cookie]) with t_cookie in X;
  rewrite <- E in X; rewrite <- X; clear X E;
  rewrite (field_at_data_at sh t_peer [StructField f; StructField I._latest_cookie]), hcf5_p5c_fa
    by auto with field_compatible.

Lemma hcf5_p5c_open_N sh q (b iv: val) (c: list val) (s: val) (lm dk mk: list val) (lk: val) :
  field_compatible t_peer [] q ->
  data_at sh t_cookie (b, (iv, (c, (s, (lm, (dk, (mk, lk))))))) (cookie_addr q) =
  (field_at sh t_peer [StructField I._birthdate; StructField I._latest_cookie] b q *
   field_at sh t_peer [StructField I._is_valid; StructField I._latest_cookie] iv q *
   data_at sh (tarray tuchar 16) c (offset_val 369 q) *
   field_at sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] s q *
   data_at sh (tarray tuchar 16) lm (offset_val 386 q) *
   data_at sh (tarray tuchar 32) dk (offset_val 402 q) *
   data_at sh (tarray tuchar 32) mk (offset_val 434 q) *
   hcf5_p5c_ckr sh q lk)%logic.
Proof.
  intros Hfc. unfold_data_at (data_at _ _ _ _).
  hcf5_p5c_sc sh I._birthdate b q.
  hcf5_p5c_sc sh I._is_valid iv q.
  hcf5_p5c_sc sh I._have_sent_mac1 s q.
  hcf5_p5c_arr sh I._cookie c q.
  hcf5_p5c_arr sh I._last_mac1_sent lm q.
  hcf5_p5c_arr sh I._cookie_decryption_key dk q.
  hcf5_p5c_arr sh I._message_mac1_key mk q.
  unfold hcf5_p5c_ckr. apply pred_ext; cancel.
Qed.
End NoiseCS.

Lemma hcf5_p5c_fW1 sh (v: val) q :
  @field_at Noise.CS sh t_peer [StructField I._birthdate; StructField I._latest_cookie] v q =
  @field_at W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] v q.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.
Lemma hcf5_p5c_fW2 sh (v: val) q :
  @field_at Noise.CS sh t_peer [StructField I._is_valid; StructField I._latest_cookie] v q =
  @field_at W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] v q.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.
Lemma hcf5_p5c_fW3 sh (v: val) q :
  @field_at Noise.CS sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] v q =
  @field_at W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] v q.
Proof.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_config_any _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

Lemma hcf5_p5c_aW sh n (v: list val) p :
  @data_at Noise.CS sh (tarray tuchar n) v p = @data_at W_config_any sh (tarray tuchar n) v p.
Proof.
  apply equal_f. apply (@data_at_change_composite Noise.CS W_config_any _ sh (tarray tuchar n) v v (JMeq_refl _)).
  prove_cs_preserve_type.
Qed.

Lemma hcf5_p5c_open sh q (b iv: val) (c: list val) (s: val) (lm dk mk: list val) (lk: val) :
  @field_compatible Noise.CS t_peer [] q ->
  @data_at Noise.CS sh t_cookie (b, (iv, (c, (s, (lm, (dk, (mk, lk))))))) (cookie_addr q) =
  (@field_at W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] b q *
   @field_at W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] iv q *
   @data_at W_config_any sh (tarray tuchar 16) c (offset_val 369 q) *
   @field_at W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] s q *
   @data_at W_config_any sh (tarray tuchar 16) lm (offset_val 386 q) *
   @data_at W_config_any sh (tarray tuchar 32) dk (offset_val 402 q) *
   @data_at W_config_any sh (tarray tuchar 32) mk (offset_val 434 q) *
   hcf5_p5c_ckr sh q lk)%logic.
Proof.
  intros Hfc. rewrite hcf5_p5c_open_N by auto. rewrite hcf5_p5c_fW1, hcf5_p5c_fW2, hcf5_p5c_fW3, !hcf5_p5c_aW. reflexivity.
Qed.

Lemma hcf5_p5c_open_ sh q : @field_compatible Noise.CS t_peer [] q ->
  @data_at_ Noise.CS sh t_cookie (cookie_addr q) =
  (@field_at_ W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] q *
   @field_at_ W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] q *
   @data_at_ W_config_any sh (tarray tuchar 16) (offset_val 369 q) *
   @field_at_ W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] q *
   @data_at_ W_config_any sh (tarray tuchar 16) (offset_val 386 q) *
   @data_at_ W_config_any sh (tarray tuchar 32) (offset_val 402 q) *
   @data_at_ W_config_any sh (tarray tuchar 32) (offset_val 434 q) *
   hcf5_p5c_ckr sh q Vundef)%logic.
Proof.
  intros Hfc.
  transitivity (@data_at Noise.CS sh t_cookie
    (Vundef, (Vundef, (Zrepeat Vundef 16, (Vundef, (Zrepeat Vundef 16, (Zrepeat Vundef 32, (Zrepeat Vundef 32, Vundef)))))))
    (cookie_addr q)); [reflexivity |].
  rewrite hcf5_p5c_open by auto. reflexivity.
Qed.

Lemma hcf5_p5c_close sh q (b iv: val) (c: list val) (s: val) (lm dk mk: list val) (lk: val) :
  @field_compatible Noise.CS t_peer [] q ->
  (@field_at W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] b q *
   @field_at W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] iv q *
   @data_at W_config_any sh (tarray tuchar 16) c (offset_val 369 q) *
   @field_at W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] s q *
   @data_at W_config_any sh (tarray tuchar 16) lm (offset_val 386 q) *
   @data_at W_config_any sh (tarray tuchar 32) dk (offset_val 402 q) *
   @data_at W_config_any sh (tarray tuchar 32) mk (offset_val 434 q) *
   hcf5_p5c_ckr sh q lk)%logic |-- @data_at_ Noise.CS sh t_cookie (cookie_addr q).
Proof. intros Hfc. rewrite <- hcf5_p5c_open by auto. apply data_at_data_at_. Qed.

Lemma hcf5_p5c_hb sh n bs p : Zlength bs = n ->
  @data_at W_config_any sh (tarray tuchar n) (bytes bs) p = hbytes sh bs p.
Proof.
  intros <-. unfold hbytes. symmetry. apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh (tarray tuchar (Zlength bs))); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p5c_zero_open sh q lk : @field_compatible Noise.CS t_peer [] q ->
  @data_at Noise.CS sh t_cookie (cookie_val cookie_zero lk) (cookie_addr q) =
  (@field_at W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] (Vlong Int64.zero) q *
   @field_at W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] (Vint Int.zero) q *
   hbytes sh (zeros 16) (offset_val 369 q) *
   @field_at W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] (Vint Int.zero) q *
   hbytes sh (zeros 16) (offset_val 386 q) *
   hbytes sh (zeros 32) (offset_val 402 q) *
   hbytes sh (zeros 32) (offset_val 434 q) *
   hcf5_p5c_ckr sh q lk)%logic.
Proof.
  intros Hfc. unfold cookie_val. cbn [ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey cookie_zero].
  rewrite hcf5_p5c_open by auto. rewrite !hcf5_p5c_hb by reflexivity. reflexivity.
Qed.

Lemma hcf5_p5c_zero_close sh q lk : @field_compatible Noise.CS t_peer [] q ->
  (@field_at W_config_any sh t_peer [StructField I._birthdate; StructField I._latest_cookie] (Vlong Int64.zero) q *
   @field_at W_config_any sh t_peer [StructField I._is_valid; StructField I._latest_cookie] (Vint Int.zero) q *
   hbytes sh (zeros 16) (offset_val 369 q) *
   @field_at W_config_any sh t_peer [StructField I._have_sent_mac1; StructField I._latest_cookie] (Vint Int.zero) q *
   hbytes sh (zeros 16) (offset_val 386 q) *
   hbytes sh (zeros 32) (offset_val 402 q) *
   hbytes sh (zeros 32) (offset_val 434 q) *
   hcf5_p5c_ckr sh q lk)%logic |-- cookie_rep sh (cookie_addr q) cookie_zero.
Proof.
  intros Hfc. rewrite <- hcf5_p5c_zero_open by auto. unfold cookie_rep. Exists lk.
  apply andp_right; [apply prop_right; unfold cookie_ok, cookie_zero; simpl; repeat split; reflexivity | apply derives_refl].
Qed.

Lemma hcf5_p5c_isz16 : is_zero (zeros 16) = true.
Proof. reflexivity. Qed.
Lemma hcf5_p5c_isz32 : is_zero (zeros 32) = true.
Proof. reflexivity. Qed.

Lemma hcf5_p5c_hqW sh v p : @data_at W_config_any sh t_hsnap v p = @data_at HCS sh t_hsnap v p.
Proof.
  symmetry. apply equal_f.
  apply (@data_at_change_composite HCS W_config_any _ sh t_hsnap); [apply JMeq_refl | prove_cs_preserve_type].
Qed.

Lemma hcf5_p5c_vdev wa D : device_rep Tsh wa D = vobjs W_config_any [VDev Tsh wa D].
Proof. unfold vobjs; simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcf5_p5c_succ T a : itable_wf T ->
  succ_in (t_L T) a = nullval \/ In (succ_in (t_L T) a) (saddrs (t_D T)).
Proof.
  intros (_ & Hinc & _). revert Hinc. generalize (t_L T) as L.
  induction L as [|x L IH]; simpl; intros Hinc; [auto|].
  destruct (EqDec_val x a).
  - destruct L as [|y L]; simpl; [auto|]. right. apply Hinc. right; left; auto.
  - apply IH. intros z Hz; apply Hinc; right; auto.
Qed.

Lemma hcf5_p5c_in L KE T : hcf5_T_ok L KE true T -> In (hs_addr (l_q L)) (saddrs (t_D T)).
Proof. intros (Hs & _). rewrite Hs. simpl. auto. Qed.

Lemma hcf5_p5c_pre L KE T HQ D : itable_wf T -> hcf5_T_ok L KE true T -> hs_sid HQ = id_addr (l_w L) ->
  Forall (vp_ok (hs_own (l_q L) T [VDev Tsh (l_w L) D]))
    (hs_ptrs (hs_snap_cur T (l_q L) (hcf5_qpeer HQ)) (hs_snap_cur T (l_q L) (hcf5_qpeer HQ))).
Proof.
  intros WF HT HS.
  destruct HT as (_ & _ & _ & _ & Hq). destruct (Hq eq_refl) as (_ & HE & _).
  unfold hs_snap_cur, snap_of, hs_ptrs, hs_ptrs_nn. cbn [sn_next sn_entry sn_hs hcf5_qpeer p_hs].
  rewrite HE. cbn [e_peer]. rewrite HS.
  unfold hs_own, vobjs_addrs. cbn [map concat vobj_addrs app].
  assert (Hs: vp_ok (l_q L :: saddrs (t_D T) ++ [l_w L; id_addr (l_w L); cc_addr (l_w L)])
                    (succ_in (t_L T) (hs_addr (l_q L)))).
  { destruct (hcf5_p5c_succ T (hs_addr (l_q L)) WF) as [N|I]; [left; auto|].
    right; right; apply in_or_app; left; auto. }
  assert (Hp: vp_ok (l_q L :: saddrs (t_D T) ++ [l_w L; id_addr (l_w L); cc_addr (l_w L)]) (l_q L))
    by (right; left; auto).
  assert (Hi: vp_ok (l_q L :: saddrs (t_D T) ++ [l_w L; id_addr (l_w L); cc_addr (l_w L)]) (id_addr (l_w L))).
  { right; right; apply in_or_app; right; simpl; auto. }
  repeat (apply Forall_cons; [assumption|]); apply Forall_nil.
Qed.

Section P5c.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P5c_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 ->
  semax (hcf5_Delta x25519) (hcf5_S5b x25519 gv L FR) hcf5_P5c
    (overridePost (hcf5_SX5 x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX. unfold hcf5_S5b, hcf5_Delta, hcf5_R, hcf5_P5c. simplify_func_tycontext. abbreviate_semax.
  unfold hcf5_F, hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW HQ.
  unfold hcf5_core, hcf5_globs, hcf5_X5b. cbn [app].
  assert_PROP (@field_compatible Noise.CS t_peer [] (l_q L)) as FCq.
  { go_lowerx. unfold hcf5_qrest. saturate_local. apply prop_right.
    match goal with Hx: field_compatible t_peer (DOT I._is_dead) _ |- _ => apply field_compatible_cons in Hx; apply Hx end. }
  rewrite (hcf5_p5c_open_ Tsh (l_q L) FCq).
  repeat flatten_sepcon_in_SEP. unfold hcf5_lvars.
  forward_call tt. Intros v.
  forward.
  forward_call tt. Intros b1.
  forward.
  forward_call (offset_val 369 (l_q L), 16, Tsh). Intros c1.
  forward_call tt. Intros b2.
  forward.
  forward_call (offset_val 386 (l_q L), 16, Tsh). Intros c2.
  forward_call (offset_val 402 (l_q L), 32, Tsh). Intros c3.
  forward_call (offset_val 434 (l_q L), 32, Tsh). Intros c4.
  sep_apply (hcf5_p5c_close Tsh (l_q L) (Vlong v)
    (Vint (if Int.eq (Int.and (Int.repr b1) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    (map (fun b : Z => Vint (Int.repr b)) c1)
    (Vint (if Int.eq (Int.and (Int.repr b2) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    (map (fun b : Z => Vint (Int.repr b)) c2) (map (fun b : Z => Vint (Int.repr b)) c3)
    (map (fun b : Z => Vint (Int.repr b)) c4) Vundef FCq).
  forward_call (Tsh, cookie_addr (l_q L)).
  unfold cookie_rep. Intros lk.
  rewrite (hcf5_p5c_zero_open Tsh (l_q L) lk FCq).
  repeat flatten_sepcon_in_SEP.
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward.
    forward_if (temp HF5._t'66 (Vint Int.one)).
    { forward. forward. entailer!. }
    { exfalso. match goal with Hx: Int64.repr 0 <> Int64.repr 0 |- _ => apply Hx; reflexivity end. }
    forward_if (temp HF5._t'67 (Vint Int.one)).
    2: { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    { forward_call (Tsh, offset_val 369 (l_q L), zeros 16).
      { cbv; discriminate. }
      rewrite hcf5_p5c_isz16. forward. entailer!. }
    forward_if (temp HF5._t'69 (Vint Int.one)).
    2: { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    { forward. forward. entailer!. }
    forward_if (temp HF5._t'70 (Vint Int.one)).
    2: { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    { forward_call (Tsh, offset_val 386 (l_q L), zeros 16).
      { cbv; discriminate. }
      rewrite hcf5_p5c_isz16. forward. entailer!. }
    forward_if (temp HF5._t'72 (Vint Int.one)).
    2: { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    { forward_call (Tsh, offset_val 402 (l_q L), zeros 32).
      { cbv; discriminate. }
      rewrite hcf5_p5c_isz32. forward. entailer!. }
    forward_if (temp HF5._t'74 (Vint Int.one)).
    2: { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    { forward_call (Tsh, offset_val 434 (l_q L), zeros 32).
      { cbv; discriminate. }
      rewrite hcf5_p5c_isz32. forward. entailer!. }
    forward_if.
    { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    forward. entailer!.
  }
  { forward. apply ENTAIL_refl. }
  assert_PROP (itable_wf T) as WF by (go_lowerx; unfold itable; normalize; apply prop_right; assumption).
  rewrite (hcf5_p5c_vdev (l_w L) D).
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, l_hq L, hs_snap_cur T (l_q L) (hcf5_qpeer HQ), Tsh, l_q L, hcf5_qpeer HQ, false,
                  Tsh, l_it L, T, [VDev Tsh (l_w L) D]).
    { assert (HT: hcf5_T_ok L KE true T) by apply H1.
      split; [repeat constructor; simpl; auto |].
      split; [eapply hcf5_p5c_in; exact HT | eapply hcf5_p5c_pre; [exact WF | exact HT | apply H0]]. }
    rewrite hcf5_snap_eqb_refl, hcf5_p5c_hqW.
    forward_if.
    { exfalso. match goal with Hx: Int.one = Int.zero |- _ => apply Int.one_not_zero; exact Hx end. }
    forward. entailer!. }
  { forward. apply ENTAIL_refl. }
  unfold POSTCONDITION, abbreviate. rewrite overridePost_normal'.
  rewrite <- (hcf5_p5c_vdev (l_w L) D).
  sep_apply (hcf5_p5c_zero_close Tsh (l_q L) lk FCq).
  unfold hcf5_SX5.
  Exists R S w D P T KE D0. Exists sn0 P0 r0 S0 w0 h0 RAW HQ.
  unfold hcf5_F, hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X5, hcf5_lvars. cbn [app].
  entailer!.
Qed.

End P5c.
