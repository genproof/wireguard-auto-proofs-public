(* law create_any: Segment F1c (hca5_fdefs.v) = the op == 1 branch body's statements 5..7 (resp_img(img__1, m__1); CHECK(r == ok && bytes_eq(img__1, exp__1, 92)); free(m__1)), from hca5_F1S2 m to hca5_SF.
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

(* at failure the harness's expectation does not depend on the index u *)
Lemma hca5_F1c_exp_u x25519 aead_enc H before r u u' :
  fst (fst (hca3_resp_exp x25519 aead_enc H before r u)) = false ->
  hca3_resp_exp x25519 aead_enc H before r u = hca3_resp_exp x25519 aead_enc H before r u'.
Proof.
  unfold hca3_resp_exp. cbv zeta. intros Hf.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl in *; auto; discriminate.
Qed.

Lemma hca5_F1c_exp_fst x25519 aead_enc H before r u u' :
  fst (fst (hca3_resp_exp x25519 aead_enc H before r u)) =
  fst (fst (hca3_resp_exp x25519 aead_enc H before r u')).
Proof.
  unfold hca3_resp_exp. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* the harness's expectation is the kernel's result *)
Lemma hca5_F1c_Y x25519 aead_enc aead_dec xaead_enc xaead_dec L P ks M S1 rr idx :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hca5_pok L P ks -> rm_ok M -> Zlength rr = 32 ->
  hca5_Y x25519 aead_enc P M S1 rr idx =
  (fst (fst (hca5_CR x25519 aead_enc P M rr idx)),
   resp_bytes (snd (fst (hca5_CR x25519 aead_enc P M rr idx))),
   snd (hca5_CR x25519 aead_enc P M rr idx)).
Proof.
  intros (_ & _ & _ & _ & HA) (_ & _ & HS & _) HM Hr.
  unfold hca5_Y, hca5_CRshim, hca5_cr_shim, hca5_CR, cr_res.
  destruct HS as (? & ? & ? & ? & ? & ? & ? & ?). destruct HM as (? & ? & ? & ?).
  specialize (HA (p_hs P) M rr idx).
  spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto.
  destruct (create_response_model x25519 aead_enc (p_hs P) M rr idx) as [[b M'] H'] eqn:EC.
  cbn [fst snd].
  destruct b.
  - destruct (Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION) eqn:Est.
    + exact HA.
    + unfold create_response_model in EC. rewrite Est in EC. discriminate.
  - destruct (Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION);
      (rewrite (hca5_F1c_exp_u _ _ _ _ _ _ idx); [exact HA | rewrite (hca5_F1c_exp_fst _ _ _ _ _ _ idx), HA; reflexivity]).
Qed.

Lemma hca5_F1c_sid x25519 aead_enc H M r idx :
  hs_sid (snd (create_response_model x25519 aead_enc H M r idx)) = hs_sid H.
Proof.
  unfold create_response_model. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hca5_F1c_u x25519 aead_enc P M S1 rr idx :
  fst (fst (hca5_CR x25519 aead_enc P M rr idx)) = true ->
  s_u32 (hca5_CRshim x25519 aead_enc P M S1 rr idx) = idx.
Proof.
  unfold hca5_CRshim, hca5_cr_shim. intros Hb. rewrite Hb.
  destruct (Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION) eqn:Eh; [reflexivity |].
  unfold hca5_CR, cr_res, create_response_model in Hb. rewrite Eh in Hb. discriminate.
Qed.

(* the shim's draws keep the counters *)
Lemma hca5_F1c_cnt P S rr b idx : hca5_cnt (hca5_cr_shim P S rr b idx) = hca5_cnt S.
Proof. unfold hca5_cr_shim. destruct (Int.eq _ _), b; reflexivity. Qed.

Lemma hca5_F1c_len M : rm_ok M -> Zlength (resp_bytes M) = 92.
Proof.
  intros (? & ? & ? & ?). unfold resp_bytes, le32. rewrite !Zlength_app, !Zlength_map. simpl.
  rewrite H, H0, H1, H2. reflexivity.
Qed.

Lemma hca5_F1c_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec _ _ _); congruence. Qed.

#[local] Instance hca5_F1c_CCE_NW : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_F1c_free sh m M : resp_rep sh m M |-- @data_at_ W_create_any sh t_resp_W m.
Proof.
  unfold resp_rep. Intros. sep_apply (@data_at_data_at_ Noise.CS).
  assert (HC: cs_preserve_type Noise.CS W_create_any (coeq Noise.CS W_create_any) t_resp = true)
    by (vm_compute; reflexivity).
  rewrite (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_resp HC) m).
  change t_resp_W with t_resp. apply derives_refl.
Qed.

Lemma hca5_F1c_hout sh bs p : Zlength bs = 92 -> hbytes sh bs p |-- hout sh 92 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hca5_F1c_hs_ok sh p P : peer_rep sh p P |-- !! hs_ok (p_hs P).
Proof. unfold peer_rep, hs_rep. entailer!. Qed.

Lemma hca5_F1c_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F1S2 x25519 aead_enc gv L FR w m)
    hca5_F1c
    (overridePost (hca5_SF x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F1S2, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R P T KS E M S1 rr idx S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite (hca5_F1c_Y x25519 aead_enc aead_dec xaead_enc xaead_dec L P (map kd_addr KS)) by auto.
  assert (Hu := hca5_F1c_u x25519 aead_enc P M S1 rr idx).
  assert (Hsid: hs_sid (snd (hca5_CR x25519 aead_enc P M rr idx)) = id_addr (l_wa L)).
  { unfold hca5_CR, cr_res. rewrite hca5_F1c_sid. apply H0. }
  assert (Hcnt: hca5_cnt (hca5_CRshim x25519 aead_enc P M S1 rr idx) = hca5_cnt S0).
  { unfold hca5_CRshim. rewrite hca5_F1c_cnt. assumption. }
  forget (hca5_CRshim x25519 aead_enc P M S1 rr idx) as S'.
  destruct (hca5_CR x25519 aead_enc P M rr idx) as [[b M'] H'] eqn:ECR.
  cbn [fst snd] in *.
  unfold hca5_F1c.
  forward_call (Tsh, l_img1 L, Ews, m, M').
  assert_PROP (rm_ok M') as HM' by (unfold resp_rep; entailer!).
  assert (Hlen := hca5_F1c_len M' HM').
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  - entailer!.
  - forward_if (temp HC._t'22 (Vint Int.one)).
    + forward_call (Tsh, l_img1 L, resp_bytes M', Tsh, l_exp1 L, resp_bytes M').
      { entailer!. simpl. rewrite Hlen. reflexivity. }
      rewrite hca5_F1c_eqb_refl. forward. entailer!.
    + exfalso. destruct b; simpl in *; (try change (Int.repr 0) with Int.zero in H8);
        rewrite Int.eq_true in H8; inv H8.
    + forward_if.
      { contradiction Int.one_not_zero. }
      forward. entailer!.
  - forward. entailer!.
  - unfold hca5_tok. sep_apply (hca5_F1c_free Ews m M').
    forward_call (t_resp_W, m, gv).
    { rewrite if_false by auto. cancel. }
    assert_PROP (hs_ok H') as HokH'.
    { sep_apply (hca5_F1c_hs_ok Tsh (l_p L) (p_set_hs P H')). entailer!. }
    sep_apply (hca5_F1c_hout Tsh (resp_bytes M') (l_img1 L) Hlen).
    sep_apply (hca5_F1c_hout Tsh (resp_bytes M') (l_exp1 L) Hlen).
    unfold hca5_SF.
    Exists R P T KS E b H' idx (if b then t_insert T (hs_addr (l_p L)) idx else T) S' S0.
    unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
    entailer!.
    destruct b; simpl; auto.
Qed.
