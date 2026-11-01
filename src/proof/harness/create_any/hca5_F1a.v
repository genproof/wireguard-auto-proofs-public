(* law create_any: Segment F1a (hca5_fdefs.v) = the op == 1 branch body's statements 0..3 (fill_resp(m__1); resp_img(before__1, m__1); bytes_copy(exp__1, before__1, 92); r = wg_noise_handshake_create_response(m__1, &p.handshake)), from hca5_F1S0 m to hca5_F1S1 m.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: the same C). *)
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
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
Require Import WgNoise.proof.harness.create_any.hca5_fdefs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_F1a_cceN : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_F1a_resp sh m : @data_at_ W_create_any sh t_resp_W m = @data_at_ Noise.CS sh t_resp m.
Proof. symmetry. exact (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_resp eq_refl) m). Qed.

Lemma hca5_F1a_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (H1 & H2 & H3 & H4). unfold resp_bytes.
  rewrite !Zlength_app, !prot_rep3_le32_len, H1, H2, H3, H4. reflexivity.
Qed.

Lemma hca5_F1a_sfind (p: val) (KS: list kdraw) (E: entry) :
  ~ In (hs_addr p) (map kd_addr KS) ->
  sfind (map (hca5_kpool p) KS ++ [(hs_addr p, Tsh, E)]) (hs_addr p) = Some (Tsh, E).
Proof.
  induction KS as [|K KS IH]; intros Hn; simpl.
  - rewrite if_true by auto. reflexivity.
  - simpl in Hn. rewrite if_false by (intros e; apply Hn; auto).
    apply IH. intros Hi; apply Hn; auto.
Qed.

Lemma hca5_F1a_inpool (p: val) (KS: list kdraw) (T: tstate) :
  hca5_pool p KS T -> hs_in_pool T p.
Proof.
  intros [[E [HD [Hp _]]] [Hnd _]]. exists E. split; [|exact Hp]. unfold t_entry. rewrite HD.
  inversion Hnd; subst. rewrite hca5_F1a_sfind by assumption. reflexivity.
Qed.

Lemma hca5_F1a_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1S0 x25519 gv L FR w m)
    hca5_F1a
    (overridePost (hca5_F1S1 x25519 aead_enc gv L FR w m) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F1S0, hca5_Delta, hca5_R, hca5_F1a. simplify_func_tycontext. abbreviate_semax.
  Intros R S P T KS E.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite hca5_F1a_resp.
  forward_call (Ews, m).
  Intros M. pose proof (hca5_F1a_len M H4) as HML.
  forward_call (Tsh, l_before1 L, Ews, m, M).
  forward_call (Tsh, l_exp1 L, Tsh, l_before1 L, resp_bytes M).
  { rewrite HML. entailer!. }
  { rewrite HML. cancel. }
  pose proof (hca5_F1a_inpool _ _ _ H1) as Hin.
  rename H0 into HPOK. pose proof HPOK as (Hpd & Hsid & Hok).
  forward_call (gv, S, w, Ews, m, M, Tsh, l_p L, P, Tsh, l_wa L, hca5_D x25519 R L, Tsh, T).
  Intros vret. destruct vret as [rr idx]; cbn [fst snd] in *.
  change (d_itab (hca5_D x25519 R L)) with (l_ita L).
  change (cr_res x25519 aead_enc P M rr idx)
    with (hca5_CR x25519 aead_enc P M rr idx) in *.
  change (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
          then (if fst (fst (hca5_CR x25519 aead_enc P M rr idx))
                then shim_u32 (shim_draw S rr) idx else shim_draw S rr) else S)
    with (hca5_CRshim x25519 aead_enc P M S rr idx).
  forward.
  unfold hca5_F1S1. Exists R P T KS E M S rr idx S.
  forget (hca5_CRshim x25519 aead_enc P M S rr idx) as S2.
  forget (hca5_CR x25519 aead_enc P M rr idx) as CR.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_lvars; cbn [app].
  destruct (fst (fst CR)) eqn:Hb; entailer!.
Qed.
