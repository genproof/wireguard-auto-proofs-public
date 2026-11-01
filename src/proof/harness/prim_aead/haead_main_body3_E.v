(* law prim_aead: main of prim_aead.h, segment E (statements 23..24: kernel decryption of ct, CHECK(ok && bytes_eq(dec, pt, n))); main.
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

Lemma hm3E_prim (sh: share) (l: list byte) (p: val) :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma hm3E_prim_back (sh: share) (l: list byte) (p: val) :
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. rewrite <- hm3E_prim. apply derives_refl. Qed.

(* an opaque equation, so that entailer!/forward do not touch the model term *)
Definition hm3E_eq {A} (u v: A) : Prop := u = v.

Lemma hm3_segE_ok {Espec: OracleKind} gv vk vxn FR : haead_hyps ->
  semax hm3_Delta (hm3_PD gv vk vxn FR) hm3_segE (overridePost (hm3_PE gv vk vxn FR) (hm3_R gv)).
Proof.
intros HH. unfold hm3_PD. Intros x key nonce xn a m. Intros ad ad_copy pt pt_copy ct rct dec.
unfold hm3_Delta, hm3_segE, hm3_R. simplify_func_tycontext. abbreviate_semax.
unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf, hm3_ranges in *. simpl app.
destruct H as (Hx & Hk & Hn & Hxn & Ha & Hm).
pose proof HH as (_ & _ & HA & HX).
assert (Hd0: x = 0 -> aead_dec key nonce a (hm3_enc x key nonce xn a m) = Some m).
{ intros ->. unfold hm3_enc. rewrite if_true by auto. apply (aead_dec_enc _ _ HA). }
assert (Hd1: x <> 0 -> xaead_dec key xn a (hm3_enc x key nonce xn a m) = Some m).
{ intros E. unfold hm3_enc. rewrite if_false by auto. apply (xaead_dec_enc _ _ HX). }
assert (Henc: Zlength (hm3_enc x key nonce xn a m) = Zlength m + 16) by (unfold hm3_enc; destruct (Z.eq_dec x 0); [apply (aead_enc_length _ _ HA) | apply (xaead_enc_length _ _ HX)]).
remember (hm3_enc x key nonce xn a m) as c eqn:Hc. change (hm3E_eq c (hm3_enc x key nonce xn a m)) in Hc.
clear HA HX HH.
rewrite <- Henc. rewrite (hm3E_prim Ews c ct), (hm3E_prim Ews a ad). Intros.
forward_if (PROP () LOCAL (temp HAC._t'20 (Vint Int.one); temp HAC._ad ad; temp HAC._ad_copy ad_copy; temp HAC._pt pt; temp HAC._pt_copy pt_copy; temp HAC._ct ct; temp HAC._rct rct; temp HAC._dec dec;
  temp HAC._x (Vint (Int.repr x)); temp HAC._nonce (Vlong (Int64.repr nonce)); temp HAC._adlen (Vlong (Int64.repr (Zlength a))); temp HAC._n (Vlong (Int64.repr (Zlength m)));
  lvar HAC._key (tarray tuchar 32) vk; lvar HAC._xnonce (tarray tuchar 24) vxn; gvars gv)
  (SEP (data_at Tsh (tarray tuchar 32) (map Vubyte key) vk;
         data_at Tsh (tarray tuchar 24) (map Vubyte xn) vxn;
         prim_bytes Ews a ad; (if Z.eq_dec (Zlength a) 0 then data_at Ews (tarray tuchar (Zlength a)) (map Vubyte a) ad else emp);
         malloc_token Ews (tarray tuchar (Zlength a)) ad; malloc_token Ews (tarray tuchar (Zlength a)) ad_copy * data_at Ews (tarray tuchar (Zlength a)) (map Vubyte a) ad_copy;
         malloc_token Ews (tarray tuchar (Zlength m)) pt * data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt;
         malloc_token Ews (tarray tuchar (Zlength m)) pt_copy * data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt_copy;
         prim_bytes Ews c ct; (if Z.eq_dec (Zlength c) 0 then data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) ct else emp);
         malloc_token Ews (tarray tuchar (Zlength c)) ct;
         malloc_token Ews (tarray tuchar (Zlength c)) rct * data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) rct;
         malloc_token Ews (tarray tuchar (Zlength m)) dec * data_at Ews (tarray tuchar (Zlength m)) (map Vubyte m) dec;
         mem_mgr gv; zero_page gv; haead_globals gv; FR))).
- forward_call (Ews, dec, Zrepeat Vundef (Zlength m), Ews, ct, c, Ews, ad, a, Tsh, vxn, xn, Tsh, vk, key, gv).
  { entailer!. simpl. rewrite Henc. reflexivity. }
  { rewrite Zlength_Zrepeat by lia. cancel. }
  { rewrite Zlength_Zrepeat by lia. lia. }
  rewrite (Hd1 H'), Zlength_Zrepeat by lia.
  forward. entailer!.
- forward_call (Ews, dec, Zrepeat Vundef (Zlength m), Ews, ct, c, Ews, ad, a, nonce, Tsh, vk, key, gv).
  { entailer!. simpl. rewrite Henc. reflexivity. }
  { rewrite Zlength_Zrepeat by lia. cancel. }
  { rewrite Zlength_Zrepeat by lia. lia. }
  assert (H0: x = 0) by (apply (f_equal Int.unsigned) in H; rewrite Int.unsigned_repr, Int.unsigned_zero in H by rep_lia; exact H).
  rewrite (Hd0 H0), Zlength_Zrepeat by lia.
  forward. entailer!.
- Intros. forward.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  + apply ENTAIL_refl.
  + forward_if (temp HAC._t'23 (Vint Int.one)).
    * forward_call (Ews, dec, m, Ews, pt, m).
      forward. rewrite if_true by auto. entailer!.
    * discriminate.
    * forward_if. { contradiction Int.one_not_zero. } forward. entailer!.
  + forward. apply ENTAIL_refl.
  + unfold POSTCONDITION, abbreviate, hm3_PE. simpl_ret_assert.
    sep_apply (hm3E_prim_back Ews a ad). sep_apply (hm3E_prim_back Ews c ct).
    unfold hm3E_eq in Hc. rewrite Henc.
    Exists x key nonce xn a m ad ad_copy pt pt_copy ct rct dec.
    unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf, hm3_ranges. simpl app. rewrite <- Hc.
    entailer!.
Qed.
