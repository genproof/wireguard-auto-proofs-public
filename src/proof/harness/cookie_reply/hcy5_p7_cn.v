(* law cookie_reply, phase P7: the cnodes of the loop over the peers and its `return 0`: a malloc'd cnode's fields, a new cnode is not one
   of the list, the loop's frame dissolves into main's stack frame. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
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
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p7_defs.
Require WgNoise.harness.x_cookie_reply.code.

Local Open Scope Z_scope.
Local Open Scope logic.

Section W.
#[local] Existing Instance W_cookie_reply.

#[local] Instance hcy5_p7_cn_cce_K : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

(* 1. a malloc'd cnode's fields *)
Lemma hcy5_p7_cn_1 sh cn :
  @data_at_ W_cookie_reply sh t_cnode5 cn |--
  @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._n] cn *
  @data_at_ CKS sh t_cksnap (offset_val 8 cn) *
  @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._next] cn.
Proof.
  assert_PROP (field_compatible t_cnode5 [] cn) by entailer!.
  rewrite data_at__eq. unfold t_cnode5 in *.
  unfold_data_at (data_at _ _ _ cn).
  rewrite (field_at_data_at sh _ (DOT HY._cs)).
  rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite (@data_at__change_composite CKS W_cookie_reply _ sh t_cksnap) by prove_cs_preserve_type.
  rewrite data_at__eq. unfold field_at_. cancel.
Qed.

(* 2. a cnode whose next field we own is not one of the list *)
Lemma hcy5_p7_cn_2 l CL v cn :
  hcy5_cns l CL * @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] v cn |--
  !! ~ In cn (map (fun x => fst (fst x)) CL).
Proof.
  revert l; induction CL as [| [[c nd] o] CL IH]; intros l; simpl.
  - entailer!.
  - Intros. subst l.
    destruct (Val.eq c cn) as [-> | Hne].
    + sep_apply (field_at_conflict Ews t_cnode5 (DOT HY._next) cn (hcy5_chead CL) v).
      { apply readable_nonidentity, writable_readable, writable_Ews. }
      rewrite FF_sepcon. apply FF_left.
    + sep_apply (IH (hcy5_chead CL)). Intros. apply prop_right. intros [? | ?]; auto.
Qed.

(* the length of a cookie (MAC: 16 bytes) *)
Lemma hcy5_p7_cn_cookie_len k s : Zlength (cookie_of k s) = 16.
Proof.
  unfold cookie_of, MAC, model.blake2s, model.b2s_digest_stream, model.b2s_out. rewrite Zlength_map. reflexivity.
Qed.

(* 3. the loop's `return 0` *)
Lemma hcy5_p7_cn_3 x25519 xaead_enc gv L FR R Q m c rp nonce rr CK CM NS PS T :
  hcy5_closeH -> hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
  hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS * itable Tsh (l_ita L) T * TT
  |-- TT * @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wa L) *
      @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wb L) *
      @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_ita L) *
      @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_itb L) *
      @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_pta L) *
      @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_ptb L) *
      @data_at_ W Tsh (Tstruct HY._m_identity noattr) (l_ib L) *
      @data_at_ W Tsh (Tstruct HY._sk_buff noattr) (l_skb L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_rawa L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_rawb L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_pub L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_secret L) *
      @data_at_ W Tsh (tarray tuchar 16) (l_cookie L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_k L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_enc L) *
      @data_at_ W Tsh (tarray tuchar 64) (l_img L) *
      @data_at_ W Tsh (tarray tuchar 64) (l_img2 L) *
      @data_at_ W Tsh (tptr (Tstruct HY._hnode noattr)) (l_peers L) *
      @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_da L) *
      @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_db L) *
      @data_at_ W Tsh (Tstruct HY._skb_snap noattr) (l_sks L) *
      @data_at_ W Tsh (Tstruct HY._shim_snap noattr) (l_ss L) *
      @data_at_ W Tsh (tarray tuchar 16) (l_pt L).
Proof.
  intros HC (HR & HQ & Hn & Hrr & HCK & HCM).
  destruct HC as (Hd & Hdc & Hit & Hpt & Hskb & Hskbc & Hmid & Hout & Hhb).
  destruct HR as (LA & LB & _).
  assert (LCK: Zlength CK = 16) by (unfold hcy5_is in HCK; subst CK; apply hcy5_p7_cn_cookie_len).
  unfold hcy5_p7_F, hcy5_p7_Fl, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0.
  simpl app. simpl fold_right_sepcon.
  sep_apply (Hd Tsh (l_wa L) (hcy5_DA x25519 R L)).
  sep_apply (Hdc Tsh (l_wb L) (hcy5_DB x25519 R L) (hcy5_CC2 x25519 R L Q rr)).
  sep_apply (Hit Tsh (l_ita L) T).
  sep_apply (Hit Tsh (l_itb L) {| t_D := []; t_L := [] |}).
  sep_apply (Hpt Tsh (l_pta L) (hcy5_phead PS)).
  sep_apply (Hpt Tsh (l_ptb L) nullval).
  sep_apply (Hmid Tsh (mident_val (hcy5_IB x25519 R)) (l_ib L)).
  sep_apply (Hskb Tsh (l_skb L) (hcy5_skb Q m)).
  sep_apply (Hhb Tsh (r_rawa R) (l_rawa L)).
  sep_apply (Hhb Tsh (r_rawb R) (l_rawb L)).
  sep_apply (Hhb Tsh CK (l_cookie L)).
  rewrite LA, LB, LCK.
  sep_apply (Hout Tsh 32 (l_pub L)). sep_apply (Hout Tsh 32 (l_secret L)).
  sep_apply (Hout Tsh 32 (l_k L)).
  sep_apply (Hout Tsh 32 (l_enc L)). sep_apply (Hout Tsh 64 (l_img L)).
  sep_apply (Hout Tsh 64 (l_img2 L)). sep_apply (Hout Tsh 16 (l_pt L)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hcy5_head NS) (l_peers L)).
  cancel.
Qed.

(* every fact at once *)
Lemma hcy5_p7_cn_all :
  (* 1. a malloc'd cnode: its fields n and next (main stores them), its snapshot (CKS, not yet taken) *)
  (forall sh cn,
     @data_at_ W_cookie_reply sh t_cnode5 cn |--
     @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._n] cn *
     @data_at_ CKS sh t_cksnap (offset_val 8 cn) *
     @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._next] cn) /\
  (* 2. a cnode whose next field we own is not one of the list *)
  (forall l CL v cn,
     hcy5_cns l CL * @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] v cn |--
     !! ~ In cn (map (fun x => fst (fst x)) CL)) /\
  (* 3. *)
  (forall x25519 xaead_enc gv L FR R Q m c rp nonce rr CK CM NS PS T,
     hcy5_closeH -> hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
     hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS * itable Tsh (l_ita L) T * TT
     |-- TT * @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wa L) *
         @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wb L) *
         @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_ita L) *
         @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_itb L) *
         @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_pta L) *
         @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_ptb L) *
         @data_at_ W Tsh (Tstruct HY._m_identity noattr) (l_ib L) *
         @data_at_ W Tsh (Tstruct HY._sk_buff noattr) (l_skb L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_rawa L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_rawb L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_pub L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_secret L) *
         @data_at_ W Tsh (tarray tuchar 16) (l_cookie L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_k L) *
         @data_at_ W Tsh (tarray tuchar 32) (l_enc L) *
         @data_at_ W Tsh (tarray tuchar 64) (l_img L) *
         @data_at_ W Tsh (tarray tuchar 64) (l_img2 L) *
         @data_at_ W Tsh (tptr (Tstruct HY._hnode noattr)) (l_peers L) *
         @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_da L) *
         @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_db L) *
         @data_at_ W Tsh (Tstruct HY._skb_snap noattr) (l_sks L) *
         @data_at_ W Tsh (Tstruct HY._shim_snap noattr) (l_ss L) *
         @data_at_ W Tsh (tarray tuchar 16) (l_pt L)).
Proof.
  split; [exact hcy5_p7_cn_1 |]. split; [exact hcy5_p7_cn_2 |]. exact hcy5_p7_cn_3.
Qed.

Lemma hcy5_p7_cn_split sh cn :
  @data_at_ W_cookie_reply sh t_cnode5 cn |--
  @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._n] cn *
  @data_at_ CKS sh t_cksnap (offset_val 8 cn) *
  @field_at_ W_cookie_reply sh t_cnode5 [StructField HY._next] cn.
Proof. apply hcy5_p7_cn_all. Qed.

Lemma hcy5_p7_cns_fresh l CL v cn :
  hcy5_cns l CL * @field_at W_cookie_reply Ews t_cnode5 [StructField HY._next] v cn |--
  !! ~ In cn (map (fun x => fst (fst x)) CL).
Proof. apply hcy5_p7_cn_all. Qed.

Lemma hcy5_p7_frame x25519 xaead_enc gv L FR R Q m c rp nonce rr CK CM NS PS T :
  hcy5_closeH -> hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM ->
  hcy5_p7_F x25519 gv L FR R Q m c rp rr CK CM NS PS * itable Tsh (l_ita L) T * TT
  |-- TT * @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wa L) *
      @data_at_ W Tsh (Tstruct HY._wg_device noattr) (l_wb L) *
      @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_ita L) *
      @data_at_ W Tsh (Tstruct HY._index_hashtable noattr) (l_itb L) *
      @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_pta L) *
      @data_at_ W Tsh (Tstruct HY._pubkey_hashtable noattr) (l_ptb L) *
      @data_at_ W Tsh (Tstruct HY._m_identity noattr) (l_ib L) *
      @data_at_ W Tsh (Tstruct HY._sk_buff noattr) (l_skb L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_rawa L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_rawb L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_pub L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_secret L) *
      @data_at_ W Tsh (tarray tuchar 16) (l_cookie L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_k L) *
      @data_at_ W Tsh (tarray tuchar 32) (l_enc L) *
      @data_at_ W Tsh (tarray tuchar 64) (l_img L) *
      @data_at_ W Tsh (tarray tuchar 64) (l_img2 L) *
      @data_at_ W Tsh (tptr (Tstruct HY._hnode noattr)) (l_peers L) *
      @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_da L) *
      @data_at_ W Tsh (Tstruct HY._dev_snap noattr) (l_db L) *
      @data_at_ W Tsh (Tstruct HY._skb_snap noattr) (l_sks L) *
      @data_at_ W Tsh (Tstruct HY._shim_snap noattr) (l_ss L) *
      @data_at_ W Tsh (tarray tuchar 16) (l_pt L).
Proof. intros. eapply hcy5_p7_cn_all; eauto. Qed.

End W.
