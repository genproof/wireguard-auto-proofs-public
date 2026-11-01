(* law cookie_reply: phase P5b of main, statements
   45..47: db.secret = secret, db.secret_birthdate = secret_birth, CHECK(dev_same(&db, &wb) && skb_same(&sks, &skb)).

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
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* Helpers                                                                 *)
(* ---------------------------------------------------------------------- *)

#[local] Instance hcy5_p5b_cce : change_composite_env CKS W_cookie_reply.
Proof. make_cs_preserve CKS W_cookie_reply. Defined.

Lemma hcy5_p5b_dsW sh v p :
  @data_at CKS sh t_devsnap v p = @data_at W_cookie_reply sh t_devsnap v p.
Proof.
  erewrite (@data_at_change_composite CKS W_cookie_reply _ sh t_devsnap _ _ (JMeq_refl _)) by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma hcy5_p5b_ssW sh v p :
  @data_at CKS sh t_skbsnap v p = @data_at W_cookie_reply sh t_skbsnap v p.
Proof.
  erewrite (@data_at_change_composite CKS W_cookie_reply _ sh t_skbsnap _ _ (JMeq_refl _)) by (vm_compute; reflexivity).
  reflexivity.
Qed.

Lemma hcy5_p5b_ddW sh v p : @data_at CKS sh t_devsnap v p |-- @data_at_ W_cookie_reply sh t_devsnap p.
Proof. rewrite hcy5_p5b_dsW. apply data_at_data_at_. Qed.

Lemma hcy5_p5b_sdW sh v p : @data_at CKS sh t_skbsnap v p |-- @data_at_ W_cookie_reply sh t_skbsnap p.
Proof. rewrite hcy5_p5b_ssW. apply data_at_data_at_. Qed.

Lemma hcy5_p5b_cc2 x R L Q rr :
  hcy5_CC2 x R L Q rr =
  mkChk (cc_secret (hcy5_CC2 x R L Q rr)) (cc_ekey (hcy5_CC1 x R L)) (cc_mkey (hcy5_CC1 x R L))
        (cc_birth (hcy5_CC2 x R L Q rr)) (cc_dev (hcy5_CC1 x R L)).
Proof. unfold hcy5_CC2, checker_rotate. destruct (birthdate_expired _ _ _); destruct (hcy5_CC1 x R L); reflexivity. Qed.

Lemma hcy5_p5b_eqb_refl l : bytes_eqb l l = true.
Proof. unfold bytes_eqb. destruct (list_eq_dec Byte.eq_dec l l); congruence. Qed.

Lemma hcy5_p5b_veqb_refl v : veqb v v = true.
Proof. unfold veqb. destruct (eq_dec v v); congruence. Qed.

Lemma hcy5_p5b_dev_eqb_refl D h : dev_eqb D h D h = true.
Proof.
  unfold dev_eqb. rewrite !hcy5_p5b_veqb_refl, !hcy5_p5b_eqb_refl, !Int64.eq_true, Bool.eqb_reflx. reflexivity.
Qed.

Lemma hcy5_p5b_skb_eqb_refl s : skb_eqb s s = true.
Proof.
  unfold skb_eqb. rewrite hcy5_p5b_veqb_refl, !hcy5_p5b_eqb_refl, Int.eq_true, Z.eqb_refl. reflexivity.
Qed.

Section P5bBytes.
Context {cs1 cs2: compspecs}.

Lemma hcy5_p5b_fc_cs: forall n p,
  @field_compatible cs1 (tarray tuchar n) nil p <-> @field_compatible cs2 (tarray tuchar n) nil p.
Proof.
  assert (A: forall (ce: composite_env) n z, align_compatible_rec ce (tarray tuchar n) z).
  { intros. apply align_compatible_rec_Tarray. intros.
    eapply align_compatible_rec_by_value; [reflexivity | apply Z.divide_1_l]. }
  intros. unfold field_compatible, size_compatible, align_compatible.
  destruct p; simpl; try tauto.
  pose proof (A (@cenv_cs cs1) n (Ptrofs.unsigned i)).
  pose proof (A (@cenv_cs cs2) n (Ptrofs.unsigned i)).
  tauto.
Qed.

Lemma hcy5_p5b_tuchar_cs: forall sh n (v: list val) p,
  @data_at cs1 sh (tarray tuchar n) v p = @data_at cs2 sh (tarray tuchar n) v p.
Proof.
  intros. unfold data_at, field_at.
  f_equal. f_equal. apply prop_ext. apply hcy5_p5b_fc_cs.
Qed.

Lemma hcy5_p5b_tuchar__cs: forall sh n p,
  @data_at_ cs1 sh (tarray tuchar n) p = @data_at_ cs2 sh (tarray tuchar n) p.
Proof. intros. unfold data_at_, field_at_. apply hcy5_p5b_tuchar_cs. Qed.
End P5bBytes.

Lemma hcy5_p5b_hW sh bs p :
  hbytes sh bs p = @data_at W_cookie_reply sh (tarray tuchar (Zlength bs)) (map Vubyte bs) p.
Proof. unfold hbytes, bytes. apply hcy5_p5b_tuchar_cs. Qed.

Lemma hcy5_p5b_houtW sh n p : hout sh n p = @data_at_ W_cookie_reply sh (tarray tuchar n) p.
Proof. unfold hout. apply hcy5_p5b_tuchar__cs. Qed.

Lemma hcy5_p5b_hbytes_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

Lemma hcy5_p5b_bytes_at sh bs p : hbytes sh bs p = bytes_at sh bs p.
Proof. unfold hbytes, bytes_at. apply hcy5_p5b_tuchar_cs. Qed.

Ltac hcy5_p5b_cs := rewrite ?hcy5_p5b_dsW, ?hcy5_p5b_ssW; cancel.

Ltac hcy5_p5b_dead :=
  exfalso;
  match goal with
  | Hf: ?x <> ?x |- _ => exact (Hf eq_refl)
  | Hf: Int.one = Int.zero |- _ => exact (Int.one_not_zero Hf)
  end.

(* db (a dev_snap) opened at the world: secret and birthdate apart, the rest *)
Definition hcy5_p5b_rest (sh: share) (D: device) (h p: val) : mpred :=
  !! field_compatible t_devsnap [] p &&
  (field_at sh t_devsnap (DOT HY._dev) (d_dev D) p *
   field_at sh t_devsnap (DOT HY._static_public) (bytes (id_pub (d_id D))) p *
   field_at sh t_devsnap (DOT HY._static_private) (bytes (id_priv (d_id D))) p *
   field_at sh t_devsnap (DOT HY._has_identity) (Val.of_bool (id_has (d_id D))) p *
   spacer sh 105 112 p *
   field_at sh t_devsnap (DOT HY._cookie_encryption_key) (bytes (cc_ekey (d_cc D))) p *
   field_at sh t_devsnap (DOT HY._message_mac1_key) (bytes (cc_mkey (d_cc D))) p *
   field_at sh t_devsnap (DOT HY._checker_device) (cc_dev (d_cc D)) p *
   field_at sh t_devsnap (DOT HY._peer_hashtable) (d_ptab D) p *
   field_at sh t_devsnap (DOT HY._index_hashtable) (d_itab D) p *
   field_at sh t_devsnap (DOT HY._peers_head) h p)%logic.

Lemma hcy5_p5b_open sh D h p :
  @data_at CKS sh t_devsnap (devsnap_val D h) p |--
  (hout sh 32 (field_address t_devsnap (DOT HY._secret) p) *
  field_at_ sh t_devsnap (DOT HY._secret_birthdate) p * hcy5_p5b_rest sh D h p)%logic.
Proof.
  rewrite hcy5_p5b_dsW.
  assert_PROP (field_compatible t_devsnap [] p) as FC by entailer!.
  unfold_data_at (data_at _ t_devsnap _ p).
  rewrite (field_at_data_at sh t_devsnap (DOT HY._secret)).
  rewrite hcy5_p5b_houtW. unfold hcy5_p5b_rest, devsnap_val. simpl fst; simpl snd.
  entailer!.
Qed.

Definition hcy5_p5b_setsb (D: device) (s: list byte) (b: int64) : device :=
  mkDev (d_dev D) (d_id D) (mkChk s (cc_ekey (d_cc D)) (cc_mkey (d_cc D)) b (cc_dev (d_cc D))) (d_ptab D) (d_itab D).

Lemma hcy5_p5b_close sh D h p s b : Zlength s = 32 ->
  (hbytes sh s (field_address t_devsnap (DOT HY._secret) p) *
  field_at sh t_devsnap (DOT HY._secret_birthdate) (Vlong b) p * hcy5_p5b_rest sh D h p)%logic |--
  @data_at CKS sh t_devsnap (devsnap_val (hcy5_p5b_setsb D s b) h) p.
Proof.
  intros Ls.
  rewrite hcy5_p5b_dsW.
  unfold hcy5_p5b_rest. Intros.
  unfold_data_at (data_at _ t_devsnap _ p).
  rewrite (field_at_data_at sh t_devsnap (DOT HY._secret)).
  rewrite hcy5_p5b_hW, Ls. unfold devsnap_val, hcy5_p5b_setsb. simpl fst; simpl snd.
  entailer!.
Qed.

Lemma hcy5_p5b_DBc2 x R L Q rr :
  hcy5_DBc x R L (hcy5_CC2 x R L Q rr) =
  hcy5_p5b_setsb (hcy5_DBc x R L (hcy5_CC1 x R L)) (cc_secret (hcy5_CC2 x R L Q rr)) (cc_birth (hcy5_CC2 x R L Q rr)).
Proof. unfold hcy5_DBc, hcy5_p5b_setsb at 1. simpl. rewrite hcy5_p5b_cc2 at 1. reflexivity. Qed.

Lemma hcy5_p5b_fold sh wg D CC :
  (hcy5_drest sh wg D * checker_rep sh (cc_addr wg) CC)%logic =
  device_rep sh wg (mkDev (d_dev D) (d_id D) CC (d_ptab D) (d_itab D)).
Proof.
  unfold hcy5_drest, device_rep. simpl. apply pred_ext; entailer!.
Qed.

Lemma hcy5_p5b_vitab sh t T : itable sh t T = vobjs W_cookie_reply [VItab sh t T].
Proof. unfold vobjs. simpl. rewrite sepcon_emp. reflexivity. Qed.

Lemma hcy5_p5b_vbytes sh bs a : hbytes sh bs a = vobjs W_cookie_reply [VBytes sh bs a].
Proof. unfold vobjs. simpl. rewrite sepcon_emp. apply hcy5_p5b_bytes_at. Qed.

Lemma hcy5_p5b_foldB x R L sh CC :
  (hcy5_drest sh (l_wb L) (hcy5_DB x R L) * checker_rep sh (cc_addr (l_wb L)) CC)%logic =
  device_rep sh (l_wb L) (hcy5_DBc x R L CC).
Proof. rewrite hcy5_p5b_fold. reflexivity. Qed.

Lemma hcy5_p5b_unfoldB x R L sh CC :
  device_rep sh (l_wb L) (hcy5_DBc x R L CC) |--
  (hcy5_drest sh (l_wb L) (hcy5_DB x R L) * checker_rep sh (cc_addr (l_wb L)) CC)%logic.
Proof. rewrite hcy5_p5b_foldB. apply derives_refl. Qed.

Lemma hcy5_p5b_vp x R L CC :
  cc_dev CC = l_wb L ->
  Forall (vp_ok ([l_wb L; d_ptab (hcy5_DBc x R L CC)] ++ vobjs_addrs [VItab Tsh (l_itb L) (mkT [] [])]))
    (dev_ptrs (hcy5_DBc x R L CC) nullval (hcy5_DBc x R L CC) nullval).
Proof.
  intros Hd. unfold dev_ptrs, hcy5_DBc, hcy5_DB, setup_dev, vobjs_addrs, vp_ok. simpl. rewrite Hd.
  repeat apply Forall_cons; try apply Forall_nil; first [left; reflexivity | right; simpl; tauto].
Qed.

Lemma hcy5_p5b_cc2dev x R L Q rr : cc_dev (hcy5_CC2 x R L Q rr) = l_wb L.
Proof. rewrite hcy5_p5b_cc2. reflexivity. Qed.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_P5b_ok {Espec: OracleKind} gv L FR :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcy5_S5 x25519 xaead_enc gv L FR) hcy5_P5b
    (overridePost (hcy5_S5b x25519 xaead_enc gv L FR) (hcy5_R gv)).
Proof.
  intros HH. unfold hcy5_S5, hcy5_Delta, hcy5_R, hcy5_P5b. simplify_func_tycontext. abbreviate_semax.
  Intros R S m c rp. Intros Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_globs, hcy5_lvars, hcy5_scrC. simpl app.
  pose proof H as (HR & HQ & HN & HRR & HCK & HCM).
  pose proof HQ as (Hn & Hmsg & _).
  assert_PROP (cc_ok (hcy5_CC2 x25519 R L Q rr)) as Hcc by (unfold checker_rep; entailer!).
  assert (LS2: Zlength (cc_secret (hcy5_CC2 x25519 R L Q rr)) = 32) by (destruct Hcc as (L1 & _); exact L1).
  set (CC1 := hcy5_CC1 x25519 R L) in *. set (CC2 := hcy5_CC2 x25519 R L Q rr) in *.
  (* bytes_copy(db.secret, secret, 32) *)
  sep_apply (hcy5_p5b_open Tsh (hcy5_DBc x25519 R L CC1) nullval (l_db L)).
  repeat flatten_sepcon_in_SEP.
  replace (hout Tsh 32 (field_address t_devsnap (DOT HY._secret) (l_db L)))
    with (hout Tsh (Zlength (cc_secret CC2)) (field_address t_devsnap (DOT HY._secret) (l_db L)))
    by (rewrite LS2; reflexivity).
  forward_call (Tsh, field_address t_devsnap (DOT HY._secret) (l_db L), Tsh, l_secret L, cc_secret CC2).
  { entailer!. rewrite LS2. simpl. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  (* db.secret_birthdate = secret_birth *)
  forward.
  sep_apply (hcy5_p5b_close Tsh (hcy5_DBc x25519 R L CC1) nullval (l_db L) (cc_secret CC2) (cc_birth CC2) LS2).
  unfold CC2. rewrite <- hcy5_p5b_DBc2. fold CC2.
  (* CHECK(dev_same(&db, &wb) && skb_same(&sks, &skb)) *)
  sep_apply (derives_refl' _ _ (hcy5_p5b_foldB x25519 R L Tsh CC2)).
  change (ptable Tsh (l_ptb L) nullval) with (ptable Tsh (d_ptab (hcy5_DBc x25519 R L CC2)) nullval).
  rewrite (hcy5_p5b_vitab Tsh (l_itb L)).
  rewrite (hcy5_p5b_vbytes Ews (q_msg Q) m).
  match goal with |- semax _ ?P _ _ => forward_loop P continue: P break: P end.
  { apply ENTAIL_refl. }
  { forward_call (Tsh, l_db L, hcy5_DBc x25519 R L CC2, nullval, Tsh, l_wb L, hcy5_DBc x25519 R L CC2, Tsh,
                  nullval, [VItab Tsh (l_itb L) (mkT [] [])]).
    { split; [constructor; [simpl; auto | constructor] |].
      apply hcy5_p5b_vp. apply hcy5_p5b_cc2dev. }
    rewrite hcy5_p5b_dev_eqb_refl.
    forward_if (temp HY._t'30 (Vint Int.one)).
    { forward_call (Tsh, l_sks L, hcy5_skb Q m, Tsh, l_skb L, hcy5_skb Q m, [VBytes Ews (q_msg Q) m]).
      { split; [constructor; [simpl; split; [auto | lia] | constructor] |].
        split.
        { destruct HQ as (_ & _ & Hp & H4 & H6 & H2 & _). unfold skb_ok, hcy5_skb; simpl; tauto. }
        unfold vobjs_addrs, vp_ok. simpl. repeat apply Forall_cons; try apply Forall_nil; right; simpl; tauto. }
      rewrite hcy5_p5b_skb_eqb_refl.
      forward. entailer!. hcy5_p5b_cs. }
    { hcy5_p5b_dead. }
    forward_if. { hcy5_p5b_dead. }
    forward. entailer!. hcy5_p5b_cs. }
  { forward. entailer!. }
  (* the post S5b: B whole again, the snapshots back to any contents *)
  unfold POSTCONDITION, abbreviate.
  match goal with |- context [RA_normal (overridePost ?Q ?R')] => change (RA_normal (overridePost Q R')) with Q end.
  rewrite <- (hcy5_p5b_vitab Tsh (l_itb L)), <- (hcy5_p5b_vbytes Ews (q_msg Q) m).
  change (ptable Tsh (d_ptab (hcy5_DBc x25519 R L CC2)) nullval) with (ptable Tsh (l_ptb L) nullval).
  sep_apply (hcy5_p5b_unfoldB x25519 R L Tsh CC2).
  sep_apply (hcy5_p5b_hbytes_out Tsh (cc_secret CC2) (l_secret L)). rewrite LS2.
  sep_apply (hcy5_p5b_ddW Tsh (devsnap_val (hcy5_DBc x25519 R L CC2) nullval) (l_db L)).
  sep_apply (hcy5_p5b_sdW Tsh (skbsnap_val (hcy5_skb Q m)) (l_sks L)).
  unfold hcy5_S5b. Exists R S m c rp. Exists Q nonce rr CK CM.
  unfold hcy5_aside0, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_snaps0, hcy5_globs, hcy5_lvars. simpl app.
  fold CC2.
  go_lower.
  apply andp_right; [apply prop_right; split; [exact H|]; rewrite !eqb_type_refl; repeat split; auto|].
  cancel.
Qed.

End Phase.
