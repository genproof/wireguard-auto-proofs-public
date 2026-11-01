(* segment C of main's loop body (statements 13..16: rc_take, the kernel decryption, the reference decryption, CHECK(ok == ref_ok)).
   States and segments: hka5_defs.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.counter.counter_spec.
Require Import WgNoise.proof.harness.transport_keepalive.hka5_defs.
Require WgNoise.proof.aead.aead_models_props3.

#[local] Existing Instance W_transport_keepalive.
Local Open Scope Z_scope.

Ltac hka5c_post := unfold hka5_LR, hka5_R;
  cbn [RA_break RA_normal loop1_ret_assert overridePost frame_ret_assert function_body_ret_assert].

Lemma hka5c_prim (sh: share) (l: list byte) (p: val) :
  data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p =
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic.
Proof.
  unfold prim_bytes. destruct (Z.eq_dec (Zlength l) 0).
  - rewrite emp_sepcon; auto.
  - rewrite sepcon_emp; auto.
Qed.

Lemma hka5c_prim_back (sh: share) (l: list byte) (p: val) :
  (prim_bytes sh l p * (if Z.eq_dec (Zlength l) 0 then data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p else emp))%logic
  |-- data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p.
Proof. rewrite <- hka5c_prim. apply derives_refl. Qed.

Lemma hka5c_po_nil sh p : @prim_out W_transport_keepalive sh [] p = emp.
Proof. reflexivity. Qed.

Lemma hka5c_pb_nil sh p : @prim_bytes W_transport_keepalive sh [] p = emp.
Proof. reflexivity. Qed.

Lemma hka5c_mb_ptr p : hka5_mb p |-- !! is_pointer_or_null p.
Proof.
  unfold hka5_mb. destruct (eq_dec p nullval).
  - subst. entailer!.
  - entailer!.
Qed.

(* the plaintext of a packet of at most 16 bytes is empty *)
Lemma hka5c_dec_empty key nonce (c: list byte) : Zlength c <= 16 ->
  (match aead_dec key nonce [] c with Some pt => map Vubyte pt | None => [] end) = [].
Proof.
  intros Hc. destruct (aead_dec key nonce [] c) as [pt|] eqn:E; [| reflexivity].
  destruct WgNoise.proof.aead.aead_models_props3.aead_models_ok3 as [HP _].
  pose proof (aead_dec_length _ _ HP _ _ _ _ _ E) as L.
  assert (Zlength c >= 16).
  { destruct (Z_lt_ge_dec (Zlength c) 16) as [Hlt|]; auto.
    rewrite (aead_dec_short _ _ HP _ _ _ _ Hlt) in E. discriminate. }
  destruct pt; [reflexivity | rewrite Zlength_cons in L; pose proof (Zlength_nonneg pt); lia].
Qed.

Lemma hka5_segC_ok {Espec: OracleKind} gv vrc vwm vsnap vkey key steps FR i top S bm ha ln nonce hdr c pkt po rp :
  semax hka5_Delta (hka5_PC gv vrc vwm vsnap vkey key steps FR i top S bm ha ln nonce hdr c pkt po rp) hka5_segC
    (overridePost (hka5_QC gv vrc vwm vsnap vkey key steps FR i top S bm ha ln nonce hdr c pkt po rp)
                  (hka5_LR gv vrc vwm vsnap vkey key steps FR)).
Proof.
  unfold hka5_Delta, hka5_PC, hka5_QC, hka5_PD, hka5_segC, hka5_tB, hka5_tl, hka5_lv, hka5_cw, hka5_fr, hka5_pkt.
  simpl app. abbreviate_semax. Intros.
  assert (Hf := H). destruct Hf as (Hi & Hs & Hk & Hc & Hha & Hln).
  pose proof (cnt_len _ _ _ Hc) as Hbm.
  forward_call (Tsh, vsnap, Tsh, vrc, top, bm).
  rewrite (hka5c_prim Ews c (offset_val 16 pkt)). Intros.
  assert_PROP (is_pointer_or_null po) as Hpo by (sep_apply (hka5c_mb_ptr po); entailer!).
  assert_PROP (is_pointer_or_null rp) as Hrp by (sep_apply (hka5c_mb_ptr rp); entailer!).
  forward_call (Ews, po, @nil val, Ews, offset_val 16 pkt, c, Ews, nullval, @nil byte, nonce, Tsh, vkey, key, gv).
  { entailer!. }
  { rewrite hka5c_po_nil, hka5c_pb_nil. cancel. }
  { rewrite !Zlength_nil. split; [rep_lia | lia]. }
  rewrite hka5c_dec_empty by assumption. rewrite hka5c_po_nil.
  (* forward_call without after_forward_call's simplification of the result (it unfolds aead_dec) *)
  rewrite <- seq_assoc. eapply semax_seq'.
  { prove_call_setup (@nil Type) funspec_sub_refl
      (Ews, rp, @nil val, Ews, offset_val 16 pkt, c, Ews, nullval, @nil byte, nonce, Tsh, vkey, key, gv).
    2: (clear_Delta_specs; clear_MORE_POST; forward_call_id1_wow).
    - entailer!.
    - rewrite !Zlength_nil. split; [rep_lia | lia]. }
  remember (aead_dec key nonce [] c) as D eqn:HD.
  after_forward_call.
  assert (HE: (match D with Some pt => map Vubyte pt | None => [] end) = []).
  { subst D. apply hka5c_dec_empty; assumption. }
  rewrite HE, hka5c_po_nil.
  forward.
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  - apply ENTAIL_refl.
  - forward_if.
    + exfalso. destruct D; simpl in *; discriminate.
    + forward. entailer!.
  - forward. apply ENTAIL_refl.
  - unfold POSTCONDITION, abbreviate. hka5c_post. unfold hka5_ok. rewrite <- HD.
    sep_apply (hka5c_prim_back Ews c (offset_val 16 pkt)).
    destruct D; entailer!.
Qed.
