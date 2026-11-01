(* law cookie_reply, phase P9, segment BA3.  honest = mode == 0; if (mode == 1) flip one byte of the reply; then the facts of the updated peers.
   Port of v1's *)
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
Require Import WgNoise.proof.harness.cookie_reply.hcy5_p9_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope Z_scope.

(* ---- helpers (prefix hcy5_p9_BA3_) ---- *)
#[local] Instance hcy5_p9_BA3_cceC : change_composite_env Cookie.CS W_cookie_reply.
Proof. make_cs_preserve Cookie.CS W_cookie_reply. Defined.

(* the reply at the world *)
Lemma hcy5_p9_BA3_cmsg_W sh p M :
  cmsg_rep sh p M = !! cm_ok M && @data_at W_cookie_reply sh t_cmsg (cmsg_val M) p.
Proof.
  unfold cmsg_rep. f_equal.
  rewrite (@data_at_change_composite Cookie.CS W_cookie_reply hcy5_p9_BA3_cceC sh t_cmsg
    (cmsg_val M) (cmsg_val M) (JMeq_refl _) eq_refl). reflexivity.
Qed.

(* supd keeps the addresses *)
Lemma hcy5_p9_BA3_addr PS a v : map peer_addr4 (supd PS a v) = map peer_addr4 PS.
Proof.
  induction PS as [| [[x sh] w] PS IH]; simpl; auto.
  destruct (EqDec_val x a); simpl; f_equal; auto.
Qed.

Lemma hcy5_p9_BA3_in_addr PS a sh P : In (a, sh, P) PS -> In a (map peer_addr4 PS).
Proof. intros H. apply (in_map peer_addr4) in H. exact H. Qed.

(* the updated peer in the combined list *)
Lemma hcy5_p9_BA3_comb (NS: list hnode4) : forall (PS: list (val * share * peer)) N a sh P v,
  In (N, (a, sh, P)) (combine NS PS) -> NoDup (map peer_addr4 PS) ->
  In (N, (a, sh, v)) (combine NS (supd PS a v)).
Proof.
  induction NS as [| N0 NS IH]; intros PS N a sh P v HIn HND; [contradiction |].
  destruct PS as [| [[x sh0] w] PS]; [contradiction |].
  simpl in HIn |- *. simpl in HND. inv HND.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct HIn as [Heq | HIn].
    + inv Heq. left. reflexivity.
    + exfalso. apply H1. apply in_combine_r in HIn. eapply hcy5_p9_BA3_in_addr; eauto.
  - destruct HIn as [Heq | HIn].
    + inv Heq. contradiction.
    + right. simpl. eapply IH; eauto.
Qed.

(* the property of every peer, after the update of the one at a *)
Lemma hcy5_p9_BA3_forall (f: val * share * peer -> Prop) (PS: list (val * share * peer)) : forall a sh P v,
  Forall f PS -> NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> f (a, sh, v) ->
  Forall f (supd PS a v).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; intros a sh P v HF HND HIn Hv; simpl; [constructor |].
  inv HF. simpl in HND. inv HND.
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct HIn as [Heq | HIn].
    + inv Heq. constructor; auto.
    + exfalso. apply H3. eapply hcy5_p9_BA3_in_addr; eauto.
  - destruct HIn as [Heq | HIn]; [inv Heq; contradiction |].
    constructor; auto. eapply IH; eauto.
Qed.

Lemma hcy5_p9_BA3_pok L KS a sh P Q : hcy5_pok L KS (a, sh, P) -> hcy5_pok L KS (a, sh, hcy5_p9_peer P Q).
Proof.
  cbv beta iota delta [hcy5_pok].
  replace (p_hs (hcy5_p9_peer P Q)) with (p_hs P) by reflexivity.
  replace (p_refs (hcy5_p9_peer P Q)) with (p_refs P) by reflexivity.
  replace (p_device (hcy5_p9_peer P Q)) with (p_device P) by reflexivity.
  replace (p_cur (hcy5_p9_peer P Q)) with (p_cur P) by reflexivity.
  replace (p_prev (hcy5_p9_peer P Q)) with (p_prev P) by reflexivity.
  replace (p_next (hcy5_p9_peer P Q)) with (p_next P) by reflexivity.
  replace (ck_dkey (p_cookie (hcy5_p9_peer P Q))) with (ck_dkey (p_cookie P)) by reflexivity.
  auto.
Qed.

(* the public-key chain: supd keeps the addresses and (for a peer with the same pubkey_next) the chain *)
Lemma hcy5_p9_BA3_phead PS a v : hcy5_phead (supd PS a v) = hcy5_phead PS.
Proof.
  destruct PS as [| [[x sh] w] PS]; simpl; auto.
  destruct (EqDec_val x a); reflexivity.
Qed.

Lemma hcy5_p9_BA3_chain (PS: list (val * share * peer)) : forall h a sh P v,
  pk_chain h PS -> In (a, sh, P) PS -> NoDup (map peer_addr4 PS) -> p_pknext v = p_pknext P ->
  pk_chain h (supd PS a v).
Proof.
  induction PS as [| [[x sh0] w] PS IH]; intros h a sh P v HC HIn HND Hk; simpl; [exact HC |].
  simpl in HC, HND. inv HND. destruct HC as [-> HC].
  destruct (EqDec_val x a) as [-> | Hne].
  - destruct HIn as [Heq | HIn].
    + inv Heq. simpl. split; [reflexivity | rewrite Hk; exact HC].
    + exfalso. apply H1. apply (in_map peer_addr4) in HIn. exact HIn.
  - destruct HIn as [Heq | HIn]; [inv Heq; contradiction |].
    simpl. split; [reflexivity |]. eapply IH; eauto.
Qed.

(* the flip's position and byte *)
Lemma hcy5_p9_BA3_kk n : 0 <= n <= Int64.max_unsigned ->
  Int64.modu (Int64.repr n) (Int64.repr (Int.signed (Int.repr 64))) = Int64.repr (n mod 64).
Proof.
  intros Hn. change (Int.signed (Int.repr 64)) with 64. unfold Int64.modu.
  rewrite Int64.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma hcy5_p9_BA3_mods b : 0 <= b <= Byte.max_unsigned ->
  Int.mods (Int.repr b) (Int.repr 255) = Int.repr (b mod 255).
Proof.
  intros Hb. unfold Byte.max_unsigned in Hb; simpl in Hb.
  unfold Int.mods. rewrite !Int.signed_repr by rep_lia.
  rewrite Z.rem_mod_nonneg by lia. reflexivity.
Qed.

Lemma hcy5_p9_BA3_d b : 0 <= b <= Byte.max_unsigned ->
  Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr 1) (Int.mods (Int.repr b) (Int.repr 255)))) =
  Int.repr (1 + b mod 255).
Proof.
  intros Hb. rewrite (hcy5_p9_BA3_mods b Hb). unfold Byte.max_unsigned in Hb; simpl in Hb.
  rewrite Int.add_unsigned, !Int.unsigned_repr by (pose proof (Z.mod_pos_bound b 255); rep_lia).
  assert (Hz: forall z, 0 <= z < 256 -> Int.zero_ext 8 (Int.repr z) = Int.repr z).
  { intros z Hz. apply Int.same_bits_eq. intros i Hi.
    rewrite Int.bits_zero_ext by lia. destruct (zlt i 8); auto.
    rewrite !Int.testbit_repr by lia. symmetry.
    apply (Z.bits_above_log2 z i). lia.
    destruct (Z.eq_dec z 0) as [-> | Hz0]; [simpl; lia |].
    assert (Z.log2 z < 8) by (apply Z.log2_lt_pow2; simpl; lia). lia. }
  pose proof (Z.mod_pos_bound b 255).
  rewrite !Hz by lia. reflexivity.
Qed.

Lemma hcy5_p9_BA3_isint x : is_int I8 Unsigned (Vubyte x).
Proof.
  unfold Vubyte. simpl. pose proof (Byte.unsigned_range_2 x).
  rewrite Int.unsigned_repr by rep_lia. rep_lia.
Qed.

(* the flipped byte: the store of (u8)(x ^ d) *)
Definition hcy5_p9_BA3_xb (x: byte) (dd: Z) : byte :=
  Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned x)) (Int.repr dd))).

Lemma hcy5_p9_BA3_xorv x dd :
  force_val (sem_cast_i2i I8 Unsigned (force_val (sem_xor tuchar tuchar (Vubyte x) (Vint (Int.repr dd))))) =
  Vubyte (hcy5_p9_BA3_xb x dd).
Proof.
  unfold Vubyte, hcy5_p9_BA3_xb. simpl. f_equal.
  set (X := Int.xor (Int.repr (Byte.unsigned x)) (Int.repr dd)).
  rewrite <- (Int.repr_unsigned (Int.zero_ext 8 X)).
  rewrite Int.zero_ext_mod by (cbn; lia).
  rewrite Byte.unsigned_repr_eq. reflexivity.
Qed.

Lemma hcy5_p9_BA3_upd l i dd : 0 <= i < Zlength l ->
  upd_Znth i (bytes l)
    (force_val (sem_cast_i2i I8 Unsigned (force_val (sem_xor tuchar tuchar (Znth i (bytes l)) (Vint (Int.repr dd)))))) =
  bytes (upd_Znth i l (hcy5_p9_BA3_xb (Znth i l) dd)).
Proof.
  intros Hi. unfold bytes. rewrite Znth_map by lia. rewrite hcy5_p9_BA3_xorv. apply upd_Znth_map.
Qed.

Section Pure.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.

(* S8's facts for the updated peers *)
Lemma hcy5_p9_BA3_inv R L Q m nonce rr CK CM NS PS T np CL KE N a P :
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE ->
  In (N, (a, Ews, P)) (combine NS PS) -> hn_addr N = np -> hs_rstatic (p_hs P) = hcy5_pubB x25519 R L ->
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS (hcy5_p9_PS PS a P Q) T np CL KE.
Proof.
  intros (Hr & (Hok & Hnp & HND & HNN & HC) & Hnpok & HT & Hcl & Hcn) HIn HN Hpub.
  unfold hcy5_p9_PS.
  assert (HInP: In (a, Ews, P) PS) by (apply in_combine_r in HIn; exact HIn).
  split; [exact Hr |]. split; [| split; [| split; [| split; [exact Hcl | exact Hcn]]]].
  - split; [| split; [| split; [| split; [exact HNN |]]]].
    + eapply hcy5_p9_BA3_forall; eauto. apply hcy5_p9_BA3_pok.
      rewrite Forall_forall in Hok. apply Hok. exact HInP.
    + unfold hnodes_peers4 in *. rewrite hcy5_p9_BA3_addr. exact Hnp.
    + rewrite hcy5_p9_BA3_addr. exact HND.
    + rewrite hcy5_p9_BA3_phead. eapply hcy5_p9_BA3_chain; eauto.
  - right. exists N, a, (hcy5_p9_peer P Q). split; [| split; [exact HN | exact Hpub]].
    eapply hcy5_p9_BA3_comb; eauto.
  - destruct HT as ((own & ix & HD & HO) & HI). split; [| exact HI].
    exists own, ix. rewrite hcy5_p9_BA3_addr. split; [exact HD | exact HO].
Qed.

(* the honest reply (mode 0) *)
Lemma hcy5_p9_BA3_honest R L Q CM NS PS T np N a P idx :
  NoDup (map peer_addr4 PS) ->
  In (N, (a, Ews, P)) (combine NS PS) -> hn_addr N = np -> hs_rstatic (p_hs P) = hcy5_pubB x25519 R L ->
  t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) -> In (hs_addr a) (t_L T) ->
  hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM (hcy5_p9_rcv CM idx) NS (hcy5_p9_PS PS a P Q) T np.
Proof.
  intros HND HIn HN Hpub He HL.
  exists N, a, (hcy5_p9_peer P Q).
  split; [eapply hcy5_p9_BA3_comb; eauto |].
  split; [exact HN |]. split; [exact Hpub |].
  split; [reflexivity |]. split; [reflexivity |].
  split; [exact He |]. split; [exact HL |]. split; reflexivity.
Qed.

End Pure.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hcy5_p9_BA3_ok {Espec: OracleKind} gv L FR R S m c rp Q nonce rr CK CM NS PS T np CL KE md N a P idx :
  hcy5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hcy5_p9_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE ->
  In (N, (a, Ews, P)) (combine NS PS) -> hn_addr N = np -> hs_rstatic (p_hs P) = hcy5_pubB x25519 R L ->
  t_entry T (hs_addr a) = Some (mkEntry a IDX_HANDSHAKE idx) -> In (hs_addr a) (t_L T) ->
  md = 0 \/ md = 1 ->
  semax (hcy5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hcy5_p9_PA x25519 gv L FR R S m c rp Q rr CK NS (hcy5_p9_PS PS a P Q) T np CL KE (hcy5_p9_rcv CM idx) md [] [])
    hcy5_p9_BA3
    (normal_ret_assert (hcy5_p9_Q1 x25519 xaead_enc gv L FR R m c rp Q nonce rr CK CM NS np CL KE)).
Proof.
  intros HH Hinv HIn HN Hpub He HL Hmd.
  unfold hcy5_Delta, hcy5_p9_PA, hcy5_p9_Q1, hcy5_p9_loc, hcy5_p9_sep, hcy5_p9_BA3.
  simplify_func_tycontext. abbreviate_semax.
  unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; simpl app.
  forward.
  pose proof Hinv as (Hr & (Hok & Hnp & HND & HNN & HC) & Hnpok & HT & Hcl & Hcn).
  pose proof (hcy5_p9_BA3_inv x25519 xaead_enc R L Q m nonce rr CK CM NS PS T np CL KE N a P Hinv HIn HN Hpub) as Hinv'.
  rewrite hcy5_p9_BA3_cmsg_W. Intros.
  destruct Hmd as [-> | ->].
  - (* mode 0: honest *)
    forward_if.
    + exfalso; lia.
    + forward.
      Exists S (hcy5_p9_PS PS a P Q) T (hcy5_p9_rcv CM idx) true.
      rewrite hcy5_p9_BA3_cmsg_W.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; cbn [app].
      entailer!.
      eapply hcy5_p9_BA3_honest; eauto.
  - (* mode 1: one byte of the reply changed *)
    forward_if; [| exfalso; auto].
    forward_call tt. Intros n.
    forward.
    forward_call tt. Intros b.
    forward.
    { entailer!. rewrite (hcy5_p9_BA3_mods b H2).
      pose proof (Z.mod_pos_bound b 255).
      rewrite Int.signed_repr by rep_lia.
      split; [rep_lia |]. intros [_ Hc]. discriminate. }
    rewrite (hcy5_p9_BA3_kk n H1).
    match goal with |- context [temp HY._d (Vint ?v)] =>
      replace v with (Int.repr (1 + b mod 255)) by (symmetry; apply (hcy5_p9_BA3_d b H2)) end.
    assert (Hk: 0 <= n mod 64 < 64) by (apply Z.mod_pos_bound; lia).
    assert (Hd: 1 <= 1 + b mod 255 <= 255) by (pose proof (Z.mod_pos_bound b 255); lia).
    set (k := n mod 64) in *. set (dd := 1 + b mod 255) in *. clearbody k dd.
    destruct H as [Hn24 He32].
    change (cm_nonce (hcy5_p9_rcv CM idx)) with (cm_nonce CM) in Hn24.
    change (cm_enc (hcy5_p9_rcv CM idx)) with (cm_enc CM) in He32.
    forward_if.
    + forward.
      forward.
      match goal with |- context [@data_at _ Ews t_cmsg ?v rp] =>
        replace v with (cmsg_val (mkCM (Int.xor (cm_type CM) (Int.repr dd)) idx (cm_nonce CM) (cm_enc CM)))
          by reflexivity end.
      Exists S (hcy5_p9_PS PS a P Q) T (mkCM (Int.xor (cm_type CM) (Int.repr dd)) idx (cm_nonce CM) (cm_enc CM)) false.
      rewrite hcy5_p9_BA3_cmsg_W.
      unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; cbn [app].
      entailer!.
      split; split; assumption.
    + forward_if.
      * forward.
        forward.
        match goal with |- context [@data_at _ Ews t_cmsg ?v rp] =>
          replace v with (cmsg_val (mkCM (cm_type CM) (Int.xor idx (Int.repr dd)) (cm_nonce CM) (cm_enc CM)))
            by reflexivity end.
        Exists S (hcy5_p9_PS PS a P Q) T (mkCM (cm_type CM) (Int.xor idx (Int.repr dd)) (cm_nonce CM) (cm_enc CM)) false.
        rewrite hcy5_p9_BA3_cmsg_W.
        unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; cbn [app].
        entailer!.
        split; split; assumption.
      * forward_if.
        -- rewrite !Int64.unsigned_repr in H, H3, H4 by rep_lia.
           forward.
           { entailer!. apply hcy5_p9_BA3_isint. }
           forward.
           match goal with |- context [@data_at _ Ews t_cmsg ?v rp] =>
             replace v with (cmsg_val (mkCM (cm_type CM) idx
               (upd_Znth (k - 8) (cm_nonce CM) (hcy5_p9_BA3_xb (Znth (k - 8) (cm_nonce CM)) dd)) (cm_enc CM))) end.
           2: { unfold cmsg_val, hcy5_p9_rcv. cbn [fst snd cm_type cm_receiver cm_nonce cm_enc].
                rewrite hcy5_p9_BA3_upd by lia. reflexivity. }
           Exists S (hcy5_p9_PS PS a P Q) T (mkCM (cm_type CM) idx
               (upd_Znth (k - 8) (cm_nonce CM) (hcy5_p9_BA3_xb (Znth (k - 8) (cm_nonce CM)) dd)) (cm_enc CM)) false.
           rewrite hcy5_p9_BA3_cmsg_W.
           unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; cbn [app].
           entailer!.
           split; split; cbn [cm_nonce cm_enc]; rewrite ?upd_Znth_Zlength by lia; assumption.
        -- rewrite !Int64.unsigned_repr in H, H3, H4 by rep_lia.
           forward.
           { entailer!. apply hcy5_p9_BA3_isint. }
           forward.
           match goal with |- context [@data_at _ Ews t_cmsg ?v rp] =>
             replace v with (cmsg_val (mkCM (cm_type CM) idx (cm_nonce CM)
               (upd_Znth (k - 32) (cm_enc CM) (hcy5_p9_BA3_xb (Znth (k - 32) (cm_enc CM)) dd)))) end.
           2: { unfold cmsg_val, hcy5_p9_rcv. cbn [fst snd cm_type cm_receiver cm_nonce cm_enc].
                rewrite hcy5_p9_BA3_upd by lia. reflexivity. }
           Exists S (hcy5_p9_PS PS a P Q) T (mkCM (cm_type CM) idx (cm_nonce CM)
               (upd_Znth (k - 32) (cm_enc CM) (hcy5_p9_BA3_xb (Znth (k - 32) (cm_enc CM)) dd))) false.
           rewrite hcy5_p9_BA3_cmsg_W.
           unfold hcy5_aside, hcy5_bside, hcy5_bufs, hcy5_pbufs, hcy5_scrB, hcy5_globs, hcy5_snaps0, hcy5_lvars; cbn [app].
           entailer!.
           split; split; cbn [cm_nonce cm_enc]; rewrite ?upd_Znth_Zlength by lia; assumption.
Qed.

End Seg.
