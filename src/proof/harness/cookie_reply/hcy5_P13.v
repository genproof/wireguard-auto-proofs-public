(* law cookie_reply: phase P13 of main, statements
   76..82: the frees (cnodes, kents_free, hnodes_free, msg, copy, reply), return 0.

   (+ its children's files). *)
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
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p13_lemmas.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* the cnode list: empty (NULL) or a pointer at the head *)
Lemma hcy5_p13_cns_local l CL :
  hcy5_cns l CL |-- !! ((CL = [] /\ l = nullval) \/ (CL <> [] /\ isptr l)).
Proof.
  destruct CL as [| [[c nd] o] CL']; simpl hcy5_cns.
  - entailer!.
  - Intros. subst l. entailer!. right. split; [discriminate | auto].
Qed.

Lemma hcy5_p13_cns_vp l CL : hcy5_cns l CL |-- valid_pointer l.
Proof.
  destruct CL as [| [[c nd] o] CL']; simpl hcy5_cns; Intros; subst l.
  - apply valid_pointer_null.
  - do 3 apply sepcon_valid_pointer1. apply sepcon_valid_pointer2.
    apply field_at_valid_ptr0; [auto | vm_compute; reflexivity | reflexivity].
Qed.

(* (as hc_hnodes_bodies3's hnodes_rep_local_facts) *)
Lemma hcy5_p13_hn_ptr l NS : hnodes_rep4 W l NS |-- !! is_pointer_or_null l.
Proof.
  destruct NS as [| N NS]; simpl.
  - entailer!.
  - Intros nx. subst l. entailer!.
    match goal with Hf: field_compatible t_hnode4 [] _ |- _ => destruct Hf as [Hp _] end.
    destruct (hn_addr N); try contradiction. exact I.
Qed.

(* the lengths of the buffers the frame gives back *)
Lemma hcy5_p13_b2s_len key outlen msg : 0 <= outlen -> Zlength (blake2s key outlen msg) = outlen.
Proof.
  intros. unfold blake2s, b2s_digest_stream, b2s_out.
  rewrite Zlength_map, Zlength_correct, upto_length. lia.
Qed.

Lemma hcy5_p13_cm_len M : cm_ok M -> Zlength (cookie_msg_bytes M) = 64.
Proof.
  intros [Hn He]. unfold cookie_msg_bytes. rewrite !Zlength_app, !prot_rep3_le32_len, Hn, He. reflexivity.
Qed.

(* the reply buffer back to its struct at the world *)
#[local] Instance hcy5_p13_cce_C : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

Lemma hcy5_p13_cmsg sh rp M : cmsg_rep sh rp M |-- @data_at_ W sh t_cmsg rp.
Proof.
  unfold cmsg_rep. Intros.
  sep_apply (@data_at_data_at_ Cookie.CS sh t_cmsg (cmsg_val M) rp).
  rewrite (@data_at__change_composite Cookie.CS W_cookie_reply _ sh t_cmsg); [apply derives_refl | prove_cs_preserve_type].
Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P13_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_closeH ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S11 x25519 xaead_enc xaead_dec gv L FR) hcy5_P13
    (overridePost (FF) (hcy5_R gv)).
Proof.
  intros HH HC. unfold hcy5_S11, hcy5_Delta, hcy5_R, hcy5_P13. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM. Intros NS PS T np CL. Intros KE CM' honest now2.
  apply hcy5_post_canon.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_lvars. simpl app.
  (* while (cns) { cn = cns->next; free(cns); cns = cn; } *)
  freeze FA := - (hcy5_cns _ _) (mem_mgr _).
  match goal with |- semax _ (PROPx _ (LOCALx (?lk :: _ :: ?Lr) _)) _ _ =>
    forward_while (EX CL1: list (val * val * option cookie),
      PROPx [] (LOCALx (lk :: temp HY._cns (hcy5_chead CL1) :: Lr)
        (SEPx [FRZL FA; hcy5_cns (hcy5_chead CL1) CL1; mem_mgr gv]))) end.
  - Exists CL. entailer!.
  - entailer!. apply denote_tc_test_eq_split; [| auto with valid_pointer].
    apply sepcon_valid_pointer1. apply sepcon_valid_pointer2. apply hcy5_p13_cns_vp.
  - destruct CL1 as [| [[c0 nd] o] CL1']; [simpl in HRE; contradiction |].
    simpl hcy5_cns. simpl hcy5_chead in *. Intros.
    assert_PROP (is_pointer_or_null (hcy5_chead CL1')) as Pn.
    { sep_apply (hcy5_p13_cns_local (hcy5_chead CL1') CL1'). entailer!.
      match goal with Hx: _ \/ _ |- _ => destruct Hx as [[_ ->]|[_ Hp]] end; [simpl; auto | apply isptr_is_pointer_or_null; auto]. }
    forward.
    forward_call (t_cnode5, c0, gv).
    { rewrite if_false by (intro; subst c0; contradiction).
      sep_apply (hcy5_p13_cnode_whole c0 nd o (hcy5_chead CL1')). cancel. }
    forward. Exists CL1'. entailer!.
  - sep_apply (hcy5_p13_cns_local (hcy5_chead CL1) CL1). Intros.
    assert (CL1 = []) as -> by (destruct H8 as [[? _]|[_ Hp]]; [auto | change (hcy5_chead CL1 = nullval) in HRE; rewrite HRE in Hp; contradiction]).
    simpl hcy5_cns. Intros. thaw FA.
  (* A's table dissolves: its struct and the pool (kents' entries, then the peers' handshake entries) *)
  pose proof HC as (Hd & Hdc & Hit & Hpt & Hskb & Hskbc & Hmid & Hout & Hhb).
  sep_apply (Hit Tsh (l_ita L) T).
  destruct H2 as ((own & ix & HD & Hown) & Hnd). rewrite HD. unfold hcy5_pool. rewrite iter_sepcon_app.
  rewrite <- (hcy5_p13_kents_snapped T KE).
  sep_apply (hcy5_p13_kents own ix (map (kent_snapped T) KE)).
  rewrite <- (hcy5_p13_khead T KE).
  assert_PROP (is_pointer_or_null (hcy5_khead (map (kent_snapped T) KE))) as Pk.
  { sep_apply (hcy5_p13_kents_ptr (hcy5_khead (map (kent_snapped T) KE)) (map (kent_snapped T) KE)). entailer!. }
  forward_call (gv, hcy5_khead (map (kent_snapped T) KE), map (kent_snapped T) KE).
  (* hnodes_free(peers): each peer with its handshake entry as a whole struct *)
  destruct (hcy5_p13_pure L (map ke_addr KE) T NS PS (hcy5_res xaead_dec T PS CM' now2) H0) as (Hn & Ha & Hsh).
  sep_apply (hcy5_p13_peers ix (hnodes_snapped4 T NS PS) (map peer_addr4 PS)
               (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) Hn Ha Hsh).
  assert_PROP (is_pointer_or_null (hcy5_head (hnodes_snapped4 T NS PS))) as Phd.
  { sep_apply (hcy5_p13_hn_ptr (hcy5_head (hnodes_snapped4 T NS PS)) (hnodes_snapped4 T NS PS)). entailer!. }
  forward.
  forward_call (gv, hcy5_head (hnodes_snapped4 T NS PS), hnodes_snapped4 T NS PS).
  (* free(msg); free(copy); free(reply) *)
  sep_apply (Hhb Ews (q_msg Q) m). sep_apply (Hhb Ews (q_msg Q) c).
  assert (Hlen: Zlength (q_msg Q) = q_n Q) by (destruct H as (_ & (_ & HL & _) & _); exact HL).
  rewrite Hlen.
  assert_PROP (isptr m /\ isptr c) as Pmc by entailer!. destruct Pmc as [Pm Pc].
  forward_call (tarray tuchar (q_n Q), m, gv).
  { rewrite if_false by (intro; subst m; contradiction). unfold hcy5_tok. cancel. }
  forward_call (tarray tuchar (q_n Q), c, gv).
  { rewrite if_false by (intro; subst c; contradiction). unfold hcy5_tok. cancel. }
  sep_apply (hcy5_p13_cmsg Ews rp CM').
  assert_PROP (isptr rp) as Prp by entailer!.
  forward_call (t_cmsg, rp, gv).
  { rewrite if_false by (intro; subst rp; contradiction). cancel. }
  forward.
  (* return 0: every local back to the stack frame *)
  destruct H as (HR & _ & _ & _ & HCK & _).
  assert (Hck: Zlength CK = 16)
    by (unfold hcy5_is in HCK; subst CK; unfold hcy5_CK, cookie_of, MAC; apply hcy5_p13_b2s_len; lia).
  pose proof (hcy5_p13_cm_len CM' H5) as Hcm.
  destruct HR as (LA & LB & _).
  sep_apply (Hd Tsh (l_wa L) (hcy5_DA x25519 R L)).
  sep_apply (Hdc Tsh (l_wb L) (hcy5_DB x25519 R L) (hcy5_CC2 x25519 R L Q rr)).
  sep_apply (Hit Tsh (l_itb L) {| t_D := []; t_L := [] |}).
  sep_apply (Hpt Tsh (l_pta L) (hcy5_phead (peers_after PS (hcy5_res xaead_dec T PS CM' now2)))).
  sep_apply (Hpt Tsh (l_ptb L) nullval).
  sep_apply (Hmid Tsh (mident_val (hcy5_IB x25519 R)) (l_ib L)).
  sep_apply (Hskb Tsh (l_skb L) (hcy5_skb Q m)).
  sep_apply (Hhb Tsh (r_rawa R) (l_rawa L)). sep_apply (Hhb Tsh (r_rawb R) (l_rawb L)).
  sep_apply (Hhb Tsh CK (l_cookie L)). sep_apply (Hhb Tsh (cookie_msg_bytes CM') (l_img L)).
  rewrite LA, LB, Hck, Hcm.
  sep_apply (Hout Tsh 32 (l_pub L)). sep_apply (Hout Tsh 32 (l_secret L)).
  sep_apply (Hout Tsh 32 (l_k L)). sep_apply (Hout Tsh 32 (l_enc L)).
  sep_apply (Hout Tsh 64 (l_img2 L)). sep_apply (Hout Tsh 16 (l_pt L)).
  sep_apply (hcy5_p13_devsnap Tsh (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L)).
  sep_apply (hcy5_p13_shimsnap Tsh (shimsnap_val S hcy5_w0) (l_ss L)).
  sep_apply (data_at_data_at_ Tsh (tptr t_hnode4) (hcy5_head (hnodes_snapped4 T NS PS)) (l_peers L)).
  simpl iter_sepcon.
  cancel.
Qed.

End Phase.
