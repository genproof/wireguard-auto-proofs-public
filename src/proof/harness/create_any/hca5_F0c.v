(* law create_any: Segment F0c (hca5_fdefs.v) = the op == 0 branch body's statements 7..9 (init_img(img, m); CHECK(r == ok && bytes_eq(img, exp, 148)); free(m)), from hca5_F0S2 m to hca5_SF.
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

Lemma hca5_F0c_tai64n_len a b : Zlength (tai64n a b) = 12.
Proof. unfold tai64n, be64, be32. rewrite !Zlength_app, !Zlength_map. reflexivity. Qed.

(* at failure the harness's expectation does not depend on the index u *)
Lemma hca5_F0c_exp_u x25519 aead_enc okid SPUB H before r ts u u' :
  fst (fst (hca3_init_exp x25519 aead_enc okid SPUB H before r ts u)) = false ->
  hca3_init_exp x25519 aead_enc okid SPUB H before r ts u = hca3_init_exp x25519 aead_enc okid SPUB H before r ts u'.
Proof.
  unfold hca3_init_exp. cbv zeta. intros Hf.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; simpl in *; auto; discriminate.
Qed.

Lemma hca5_F0c_exp_fst x25519 aead_enc okid SPUB H before r ts u u' :
  fst (fst (hca3_init_exp x25519 aead_enc okid SPUB H before r ts u)) =
  fst (fst (hca3_init_exp x25519 aead_enc okid SPUB H before r ts u')).
Proof.
  unfold hca3_init_exp. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

(* the harness's expectation is the kernel's result *)
Lemma hca5_F0c_X x25519 aead_enc aead_dec xaead_enc xaead_dec R L P ks M S1 rr idx :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> hca5_pok L P ks -> im_ok M -> Zlength rr = 32 ->
  hca5_X x25519 aead_enc R L P M S1 rr idx =
  (fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)),
   init_bytes (snd (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx))),
   snd (hca5_CI x25519 aead_enc R L P M S1 rr idx)).
Proof.
  intros (HX & _ & _ & HA & _) (_ & _ & HS & _) HM Hr.
  unfold hca5_X, hca5_CIshim, hca5_ci_shim, hca5_CI, ci_res.
  assert (Hid: id_has (d_id (hca5_D x25519 R L)) = mi_ok (hca5_I x25519 R)) by reflexivity.
  rewrite <- Hid.
  set (ID := d_id (hca5_D x25519 R L)).
  assert (Hpub: Zlength (id_pub ID) = 32).
  { subst ID. unfold hca5_D, setup_dev, setup_identity, identity_of. simpl.
    destruct (memneq_bool _ _); [apply HX | reflexivity]. }
  clearbody ID.
  destruct HS as (? & ? & ? & ? & ? & ? & ? & ?). destruct HM as (? & ? & ? & ? & ?).
  specialize (HA ID (p_hs P) M rr (tai64n (s_rsec S1) (s_rnsec S1)) idx).
  spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto. spec HA; auto.
  spec HA; auto. spec HA; auto. spec HA; auto. spec HA; [apply hca5_F0c_tai64n_len |].
  destruct (create_initiation_model x25519 aead_enc ID (p_hs P) M rr (tai64n (s_rsec S1) (s_rnsec S1)) idx)
    as [[b M'] H'] eqn:EC.
  cbn [fst snd].
  destruct b.
  - destruct (id_has ID) eqn:Ehas.
    + exact HA.
    + unfold create_initiation_model in EC. rewrite Ehas in EC. discriminate.
  - destruct (id_has ID); (rewrite (hca5_F0c_exp_u _ _ _ _ _ _ _ _ _ idx); [exact HA | rewrite (hca5_F0c_exp_fst _ _ _ _ _ _ _ _ _ idx), HA; reflexivity]).
Qed.

Lemma hca5_F0c_sid x25519 aead_enc ID H M r ts idx :
  hs_sid (snd (create_initiation_model x25519 aead_enc ID H M r ts idx)) = hs_sid H.
Proof.
  unfold create_initiation_model. cbv zeta.
  repeat match goal with |- context [if ?c then _ else _] => destruct c end; reflexivity.
Qed.

Lemma hca5_F0c_u x25519 aead_enc R L P M S1 rr idx :
  fst (fst (hca5_CI x25519 aead_enc R L P M S1 rr idx)) = true ->
  s_u32 (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) = idx.
Proof.
  unfold hca5_CIshim, hca5_ci_shim. intros Hb. rewrite Hb.
  destruct (id_has (d_id (hca5_D x25519 R L))) eqn:Eh; [reflexivity |].
  unfold hca5_CI, ci_res, create_initiation_model in Hb. rewrite Eh in Hb. discriminate.
Qed.

(* the shim's draws keep the counters *)
Lemma hca5_F0c_cnt D S rr b idx : hca5_cnt (hca5_ci_shim D S rr b idx) = hca5_cnt S.
Proof. unfold hca5_ci_shim. destruct (id_has _), b; reflexivity. Qed.

Lemma hca5_F0c_len M : im_ok M -> Zlength (init_bytes M) = 148.
Proof.
  intros (? & ? & ? & ? & ?). unfold init_bytes, le32. rewrite !Zlength_app, !Zlength_map. simpl.
  rewrite H, H0, H1, H2, H3. reflexivity.
Qed.

Lemma hca5_F0c_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec _ _ _); congruence. Qed.

#[local] Instance hca5_F0c_CCE_NW : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_F0c_free sh m M : init_rep sh m M |-- @data_at_ W_create_any sh t_init_W m.
Proof.
  unfold init_rep. Intros. sep_apply (@data_at_data_at_ Noise.CS).
  assert (HC: cs_preserve_type Noise.CS W_create_any (coeq Noise.CS W_create_any) t_init = true)
    by (vm_compute; reflexivity).
  rewrite (equal_f (@data_at__change_composite Noise.CS W_create_any _ sh t_init HC) m).
  change t_init_W with t_init. apply derives_refl.
Qed.

Lemma hca5_F0c_hout sh bs p : Zlength bs = 148 -> hbytes sh bs p |-- hout sh 148 p.
Proof. intros Hl. unfold hbytes, hout. rewrite Hl. apply data_at_data_at_. Qed.

Lemma hca5_F0c_hs_ok sh p P : peer_rep sh p P |-- !! hs_ok (p_hs P).
Proof. unfold peer_rep, hs_rep. entailer!. Qed.

Lemma hca5_F0c_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) (m: val) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_F0S2 x25519 aead_enc gv L FR w m)
    hca5_F0c
    (overridePost (hca5_SF x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_F0S2, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R P T KS E M S1 rr idx S0.
  unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  rewrite (hca5_F0c_X x25519 aead_enc aead_dec xaead_enc xaead_dec R L P (map kd_addr KS)) by auto.
  assert (Hu := hca5_F0c_u x25519 aead_enc R L P M S1 rr idx).
  assert (Hsid: hs_sid (snd (hca5_CI x25519 aead_enc R L P M S1 rr idx)) = id_addr (l_wa L)).
  { unfold hca5_CI, ci_res. rewrite hca5_F0c_sid. apply H0. }
  assert (Hcnt: hca5_cnt (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) = hca5_cnt S0).
  { unfold hca5_CIshim. rewrite hca5_F0c_cnt. assumption. }
  forget (hca5_CIshim x25519 aead_enc R L P M S1 rr idx) as S'.
  destruct (hca5_CI x25519 aead_enc R L P M S1 rr idx) as [[b M'] H'] eqn:ECI.
  cbn [fst snd] in *.
  unfold hca5_F0c.
  forward_call (Tsh, l_img L, Ews, m, M').
  assert_PROP (im_ok M') as HM' by (unfold init_rep; entailer!).
  assert (Hlen := hca5_F0c_len M' HM').
  match goal with |- semax _ ?Pre _ _ => forward_loop Pre continue: Pre break: Pre end.
  - entailer!.
  - forward_if (temp HC._t'15 (Vint Int.one)).
    + forward_call (Tsh, l_img L, init_bytes M', Tsh, l_exp L, init_bytes M').
      { entailer!. simpl. rewrite Hlen. reflexivity. }
      rewrite hca5_F0c_eqb_refl. forward. entailer!.
    + exfalso. destruct b; simpl in *; (try change (Int.repr 0) with Int.zero in H8);
        rewrite Int.eq_true in H8; inv H8.
    + forward_if.
      { contradiction Int.one_not_zero. }
      forward. entailer!.
  - forward. entailer!.
  - unfold hca5_tok. sep_apply (hca5_F0c_free Ews m M').
    forward_call (t_init_W, m, gv).
    { rewrite if_false by auto. cancel. }
    assert_PROP (hs_ok H') as HokH'.
    { sep_apply (hca5_F0c_hs_ok Tsh (l_p L) (p_set_hs P H')). entailer!. }
    sep_apply (hca5_F0c_hout Tsh (init_bytes M') (l_img L) Hlen).
    sep_apply (hca5_F0c_hout Tsh (init_bytes M') (l_exp L) Hlen).
    unfold hca5_SF.
    Exists R P T KS E b H' idx (if b then t_insert T (hs_addr (l_p L)) idx else T) S' S0.
    unfold hca5_world, hca5_globs, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
    entailer!.
    destruct b; simpl; auto.
Qed.
