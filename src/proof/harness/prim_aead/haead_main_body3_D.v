(* law prim_aead: main of prim_aead.h, segment D (statements 21..22: kernel + reference encryption, CHECK(bytes_eq(ct, rct, n + 16))); main.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require Import WgNoise.proof.harness.prim_aead.haead_main_body3_defs.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

Lemma hm3D_prim (sh: share) (l: list byte) (p: val) :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma hm3D_prim_back (sh: share) (l: list byte) (p: val) :
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. rewrite <- hm3D_prim. apply derives_refl. Qed.

Lemma hm3_segD_ok {Espec: OracleKind} gv vk vxn FR : haead_hyps ->
  semax hm3_Delta (hm3_PC gv vk vxn FR) hm3_segD (overridePost (hm3_PD gv vk vxn FR) (hm3_R gv)).
Proof.
intros HH. unfold hm3_PC. Intros x key nonce xn a m. Intros ad ad_copy pt pt_copy ct rct dec.
unfold hm3_Delta, hm3_segD, hm3_R. simplify_func_tycontext. abbreviate_semax.
unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf, hm3_ranges in *. simpl app.
match goal with H: _ /\ _ /\ _ /\ _ /\ _ /\ _ |- _ => destruct H as (Hx & Hk & Hn & Hxn & Ha & Hm) end.
pose proof HH as (_ & _ & HA & HX).
assert (Henc: Zlength (hm3_enc x key nonce xn a m) = Zlength m + 16) by (unfold hm3_enc; destruct (Z.eq_dec x 0); [apply (aead_enc_length _ _ HA) | apply (xaead_enc_length _ _ HX)]).
forward_if (PROP () LOCAL (temp HAC._ad ad; temp HAC._ad_copy ad_copy; temp HAC._pt pt; temp HAC._pt_copy pt_copy; temp HAC._ct ct; temp HAC._rct rct; temp HAC._dec dec;
  temp HAC._x (Vint (Int.repr x)); temp HAC._nonce (Vlong (Int64.repr nonce)); temp HAC._adlen (Vlong (Int64.repr (Zlength a))); temp HAC._n (Vlong (Int64.repr (Zlength m)));
  lvar HAC._key (tarray tuchar 32) vk; lvar HAC._xnonce (tarray tuchar 24) vxn; gvars gv)
  (SEP (data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         hm3_buf (Zlength a) (map Vubyte a) ad; hm3_buf (Zlength a) (map Vubyte a) ad_copy;
         hm3_buf (Zlength m) (map Vubyte m) pt; hm3_buf (Zlength m) (map Vubyte m) pt_copy;
         hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) ct; hm3_buf (Zlength m + 16) (map Vubyte (hm3_enc x key nonce xn a m)) rct;
         hm3_buf (Zlength m) (Zrepeat Vundef (Zlength m)) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR))).
- Intros. rewrite (hm3D_prim Ews m pt), (hm3D_prim Ews a ad). Intros.
  forward_call (Ews, ct, Ews, pt, m, Ews, ad, a, Tsh, vxn, xn, Tsh, vk, key, gv).
  sep_apply (hm3D_prim_back Ews m pt). sep_apply (hm3D_prim_back Ews a ad).
  forward_call (Ews, rct, Ews, pt, m, Ews, ad, a, Tsh, vxn, xn, Tsh, vk, key, gv).
  entailer!. unfold hm3_enc, hm3_buf. rewrite if_false by auto. cancel.
- assert (x = 0) by (destruct (Z.eq_dec x 0); auto; assert (x = 1) by lia; subst; discriminate). subst x.
  Intros. rewrite (hm3D_prim Ews m pt), (hm3D_prim Ews a ad). Intros.
  forward_call (Ews, ct, Ews, pt, m, Ews, ad, a, nonce, Tsh, vk, key, gv).
  sep_apply (hm3D_prim_back Ews m pt). sep_apply (hm3D_prim_back Ews a ad).
  forward_call (Ews, rct, Ews, pt, m, Ews, ad, a, nonce, Tsh, vk, key, gv).
  entailer!. unfold hm3_enc, hm3_buf. rewrite if_true by auto. cancel.
- unfold hm3_buf. Intros.
  set (E := hm3_enc x key nonce xn a m) in *.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  + apply ENTAIL_refl.
  + rewrite <- Henc. forward_call (Ews, ct, E, Ews, rct, E).
    { entailer!. simpl. rewrite Henc. reflexivity. }
    rewrite if_true by auto.
    forward_if; [discriminate |]. forward. rewrite Henc. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold hm3_PD. Exists x key nonce xn a m. Exists ad ad_copy pt pt_copy ct rct dec.
    unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf, hm3_ranges. simpl app. entailer!.
Qed.
