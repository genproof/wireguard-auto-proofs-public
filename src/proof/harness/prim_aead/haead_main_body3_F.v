(* law prim_aead: main of prim_aead.h, segment F (statements 25..34: check_decrypt_any, CHECK(copies), the seven frees, return 0); main.
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

Lemma hm3_segF_ok {Espec: OracleKind} gv vk vxn FR : haead_hyps ->
  semax hm3_Delta (hm3_PE gv vk vxn FR) hm3_segF (overridePost FF (hm3_R gv)).
Proof.
intros HH. unfold hm3_PE. Intros x key nonce xn a m. Intros ad ad_copy pt pt_copy ct rct dec.
unfold hm3_Delta, hm3_segF, hm3_R. apply hm3_post_canon. simplify_func_tycontext. abbreviate_semax.
unfold hm3_tB, hm3_tA, hm3_lv, hm3_buf, hm3_ranges in *. simpl app.
destruct H as (Hx & Hk & Hn & Hxn & Ha & Hm).
pose proof HH as (_ & _ & HA & HX).
assert (Henc: Zlength (hm3_enc x key nonce xn a m) = Zlength m + 16) by (unfold hm3_enc; destruct (Z.eq_dec x 0); [apply (aead_enc_length _ _ HA) | apply (xaead_enc_length _ _ HX)]).
remember (hm3_enc x key nonce xn a m) as c eqn:Hc. clear Hc HA HX HH.
rewrite <- Henc. Intros.
forward_call (x, Tsh, vk, key, nonce, Tsh, vxn, xn, Ews, ad, a, Ews, ct, c, gv).
{ entailer!. simpl. replace (Zlength c - 16) with (Zlength m) by lia. reflexivity. }
assert_PROP (isptr ad /\ isptr ad_copy /\ isptr pt /\ isptr pt_copy /\ isptr ct /\ isptr rct /\ isptr dec) as Hp
  by (rewrite Henc in *; entailer!).
destruct Hp as (Pa & Pac & Pp & Ppc & Pc & Prc & Pd).
match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
{ apply ENTAIL_refl. }
{ forward_call (Ews, ad, a, Ews, ad_copy, a).
  rewrite if_true by auto.
  forward_if (temp HAC._t'26 (Vint Int.one)).
  - forward_call (Ews, pt, m, Ews, pt_copy, m).
    rewrite if_true by auto. forward. entailer!.
  - discriminate.
  - forward_if True; [ discriminate | forward; entailer! | ].
    forward. entailer!. }
forward_call (tarray tuchar (Zlength a), ad, gv).
{ rewrite if_false by (destruct ad; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength a)) (map Vubyte a) ad). cancel. }
forward_call (tarray tuchar (Zlength a), ad_copy, gv).
{ rewrite if_false by (destruct ad_copy; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength a)) (map Vubyte a) ad_copy). cancel. }
forward_call (tarray tuchar (Zlength m), pt, gv).
{ rewrite if_false by (destruct pt; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt). cancel. }
forward_call (tarray tuchar (Zlength m), pt_copy, gv).
{ rewrite if_false by (destruct pt_copy; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength m)) (map Vubyte m) pt_copy). cancel. }
forward_call (tarray tuchar (Zlength c), ct, gv).
{ rewrite if_false by (destruct ct; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength c)) (map Vubyte c) ct). cancel. }
forward_call (tarray tuchar (Zlength c), rct, gv).
{ rewrite if_false by (destruct rct; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength c)) (map Vubyte c) rct). cancel. }
forward_call (tarray tuchar (Zlength m), dec, gv).
{ rewrite if_false by (destruct dec; try contradiction; discriminate).
  sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength m)) (map Vubyte m) dec). cancel. }
forward.
sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte key) vk).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 24) (map Vubyte xn) vxn).
cancel.
Qed.
