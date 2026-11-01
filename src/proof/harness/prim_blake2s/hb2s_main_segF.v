(* main of law prim_blake2s, segment F (statements 24..32): the one-shot blake2s, CHECK(out2 == ref),
   CHECK(msg == copy && key == key_copy), the five frees, return 0. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_spec.
Require Import WgNoise.proof.harness.prim_blake2s.hb2s_main_defs.
Require WgNoise.harness.x_prim_blake2s.code.

#[local] Existing Instance W_prim_blake2s.
Local Open Scope Z_scope.

Lemma hb2s_F_blake2s_len key outlen msg : 0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out. rewrite Zlength_map, Zlength_correct, upto_length.
  rep_lia.
Qed.

(* a byte buffer as the input of blake2s (the empty one stays in the frame) *)
Lemma hb2s_F_bytes sh l p :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (b2s_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold b2s_bytes. if_tac.
  - rewrite emp_sepcon. reflexivity.
  - rewrite sepcon_emp. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
Qed.

Lemma hb2s_F_out sh n p :
  data_at sh (tarray tuchar n) (Zrepeat Vundef n) p = @data_at_ Blake2s.CS sh (tarray tuchar n) p.
Proof.
  rewrite <- (@WgNoise.proof.libc.libc_bytes.data_at__tarray_tuchar_cs W_prim_blake2s).
  unfold data_at_, field_at_, data_at. reflexivity.
Qed.

Definition hb2s_F_kptr (keylen: Z) (p: val) : val := if zlt 0 keylen then p else nullval.

Definition hb2s_F_krest (sh: share) (kb: list byte) (keylen: Z) (p: val) : mpred :=
  if zlt 0 keylen
  then data_at sh (tarray tuchar (32 - keylen)) (sublist keylen 32 (map Vubyte kb))
         (field_address0 (tarray tuchar 32) [ArraySubsc keylen] p)
  else data_at sh (tarray tuchar 32) (map Vubyte kb) p.

(* the key array split at keylen *)
Lemma hb2s_F_key sh kb keylen p :
  0 <= keylen <= 32 -> Zlength kb = 32 ->
  data_at sh (tarray tuchar 32) (map Vubyte kb) p =
  (b2s_bytes sh (sublist 0 keylen kb) (hb2s_F_kptr keylen p) * hb2s_F_krest sh kb keylen p)%logic.
Proof.
  intros Hk Hkb. unfold hb2s_F_kptr, hb2s_F_krest. destruct (zlt 0 keylen).
  - rewrite (split2_data_at_Tarray_tuchar sh 32 keylen) by (try lia; rewrite Zlength_map; lia).
    rewrite b2s_bytes_nonempty by (rewrite Zlength_sublist; lia).
    rewrite Zlength_sublist by lia. rewrite Z.sub_0_r, sublist_map.
    f_equal. apply WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs.
  - replace keylen with 0 by lia. rewrite sublist_nil, b2s_bytes_nil, emp_sepcon. reflexivity.
Qed.

(* main's post (TT) in the canonical form forward needs for the return *)
Lemma hb2s_F_post_canon {Espec: OracleKind} {cs: compspecs} Delta P c Q (SF: environ -> mpred) (gv: globals) :
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint
                     (PROP () LOCAL () SEP (TT))) SF)) ->
  semax Delta P c (overridePost Q (frame_ret_assert (function_body_ret_assert tint (hb2s_post gv)) SF)).
Proof.
  intros H. eapply semax_post; [.. | exact H]; intros; simpl.
  all: intros rho; apply andp_left2; try apply derives_refl.
  apply sepcon_derives; [| apply derives_refl].
  unfold bind_ret, hb2s_post. destruct vl; [| simpl; apply derives_refl].
  simpl. unfold_lift. apply andp_derives; [apply derives_refl | apply TT_right].
Qed.

Lemma hb2s_segF_ok {Espec: OracleKind} gv vctx vkey vkc FR :
  semax hb2s_Delta (hb2s_PE gv vctx vkey vkc FR) hb2s_segF (overridePost FF (hb2s_R gv)).
Proof.
  unfold hb2s_PE. Intros outlen keylen n kb mb msg copy out ref out2.
  unfold hb2s_Delta, hb2s_segF, hb2s_R. apply hb2s_F_post_canon.
  simplify_func_tycontext. abbreviate_semax.
  unfold hb2s_buf, hb2s_ranges, hb2s_tv, hb2s_lv in *. Intros. simpl app.
  destruct H as (Hol & Hkl & Hkb & Hn). subst n.
  forward_if (temp HC._t'22 (hb2s_F_kptr keylen vkey)); [forward; entailer! .. | ].
  { unfold hb2s_F_kptr. rewrite !Int64.unsigned_repr in H by rep_lia. rewrite if_true by lia. reflexivity. }
  { unfold hb2s_F_kptr. rewrite !Int64.unsigned_repr in H by rep_lia. rewrite if_false by lia. reflexivity. }
  rewrite (hb2s_F_key Tsh kb keylen vkey) by auto.
  rewrite (hb2s_F_bytes Ews mb msg).
  rewrite (hb2s_F_out Ews outlen out2).
  flatten_sepcon_in_SEP. flatten_sepcon_in_SEP.
  forward_call (Tsh, hb2s_F_kptr keylen vkey, sublist 0 keylen kb, Ews, msg, mb, Ews, out2, outlen, gv).
  { entailer!. rewrite Zlength_sublist by lia. rewrite Z.sub_0_r. unfold hb2s_F_kptr.
    destruct (zlt 0 keylen); destruct vkey; try contradiction; reflexivity. }
  { rewrite Zlength_sublist by lia. lia. }
  rewrite <- (@WgNoise.proof.libc.libc_bytes.data_at_tarray_tuchar_cs W_prim_blake2s Blake2s.CS).
  gather_SEP (b2s_bytes Tsh _ _) (hb2s_F_krest _ _ _ _). rewrite <- hb2s_F_key by auto.
  gather_SEP (b2s_bytes Ews _ _) (if Z.eq_dec _ _ then _ else _). rewrite <- hb2s_F_bytes.
  set (B := blake2s (sublist 0 keylen kb) outlen mb).
  assert (HB: Zlength B = outlen) by (apply hb2s_F_blake2s_len; lia).
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { rewrite <- HB.
    forward_call (Ews, out2, B, Ews, ref, B).
    rewrite if_true by auto.
    forward_if True; [ discriminate | forward; entailer! | ].
    forward. rewrite HB. entailer!. }
  match goal with |- semax _ ?P _ _ => forward_loop P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Ews, msg, mb, Ews, copy, mb).
    rewrite if_true by auto.
    forward_if (temp HC._t'25 (Vint Int.one)).
    - forward_call (Tsh, vkey, kb, Tsh, vkc, kb).
      + entailer!. rewrite Hkb. reflexivity.
      + rewrite Hkb. cancel.
      + rewrite if_true by auto. rewrite Hkb. forward. entailer!.
    - discriminate.
    - forward_if True; [ discriminate | forward; entailer! | ].
      forward. entailer!. }
  assert_PROP (isptr msg /\ isptr copy /\ isptr out /\ isptr ref /\ isptr out2) as Hp by entailer!.
  destruct Hp as (Pm & Pc & Po & Pr & Po2).
  forward_call (tarray tuchar (Zlength mb), msg, gv).
  { rewrite if_false by (destruct msg; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) msg). cancel. }
  forward_call (tarray tuchar (Zlength mb), copy, gv).
  { rewrite if_false by (destruct copy; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar (Zlength mb)) (map Vubyte mb) copy). cancel. }
  forward_call (tarray tuchar outlen, out, gv).
  { rewrite if_false by (destruct out; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar outlen) (map Vubyte B) out). cancel. }
  forward_call (tarray tuchar outlen, ref, gv).
  { rewrite if_false by (destruct ref; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar outlen) (map Vubyte B) ref). cancel. }
  forward_call (tarray tuchar outlen, out2, gv).
  { rewrite if_false by (destruct out2; try contradiction; discriminate).
    sep_apply (data_at_data_at_ Ews (tarray tuchar outlen) (map Vubyte B) out2). cancel. }
  forward.
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkey).
  sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (map Vubyte kb) vkc).
  unfold t_hctx. cancel.
Qed.
