(* law create_any: Segment C = statements 11..14 (hs_randomize(&p.handshake); peer_randomize_rest(&p); p.refcount.refcount = draw_peer_refs(); if (nondet_u8() & 1) wg_index_hashtable_insert(&ita, &p.handshake.entry)), from hca5_SB to hca5_SB.
   (states, conventions), spec-create_any3 (v1 notes of the same segment); v1 proof of the
   segment: (port it: same C where the C did not change). *)
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
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.create_any.hca3_model.
Require Import WgNoise.proof.harness.create_any.hca5_spec.
Require Import WgNoise.proof.harness.create_any.hca5_defs.
#[local] Existing Instance W_create_any.
Local Open Scope logic.

#[local] Instance hca5_PC_CCE : change_composite_env Noise.CS W_create_any.
Proof. make_cs_preserve Noise.CS W_create_any. Defined.

Lemma hca5_PC_refs_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at Noise.CS sh t_peer [StructField I._refcount; StructField I._refcount] (Vint v) p.
Proof.
  unfold_field_at 1%nat. reflexivity.
Qed.

Lemma hca5_PC_refs_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at W_create_any sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount; StructField HC._refcount] (Vint v) p.
Proof.
  rewrite hca5_PC_refs_nest.
  change (Tstruct HC._wg_peer noattr) with t_peer. change HC._refcount with I._refcount.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_create_any _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

(* peer_rep without its reference count *)
Definition hca5_PC_prest (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   @field_at Noise.CS sh t_peer [StructField I._is_dead] (Val.of_bool (p_dead P)) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong (p_lsh P)) p *
   cookie_rep sh (cookie_addr p) (p_cookie P) *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p).

Lemma hca5_PC_split sh p P :
  peer_rep sh p P = hca5_PC_prest sh p P *
    field_at sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount; StructField HC._refcount] (Vint (p_refs P)) p.
Proof.
  unfold peer_rep, hca5_PC_prest. rewrite <- hca5_PC_refs_conv.
  apply pred_ext; Intros; entailer!; cancel.
Qed.

Lemma hca5_PC_fold sh p P r :
  hca5_PC_prest sh p P *
    field_at sh (Tstruct HC._wg_peer noattr) [StructField HC._refcount; StructField HC._refcount] (Vint r) p
  = peer_rep sh p (p_set_refs P r).
Proof. rewrite hca5_PC_split. reflexivity. Qed.

Lemma hca5_PC_pool_insert (p: val) (T: tstate) (idx: int) :
  hca5_pool p [] T -> hca5_pool p [] (t_insert T (hs_addr p) idx).
Proof.
  intros [[E [HD [HP HT]]] [Hnd Hinc]]; simpl in HD.
  split; [| split; [exact Hnd | intros a Ha; inversion Ha]].
  exists (mkEntry (e_peer E) (e_type E) idx).
  unfold t_insert, t_set_index, t_entry, t_upd. rewrite HD. simpl.
  destruct (EqDec_val (hs_addr p) (hs_addr p)) as [_|n]; [| congruence].
  simpl. auto.
Qed.

Lemma hca5_PC_raw_ok (p: val) (T: tstate) :
  hca5_pool p [] T -> In (hs_addr p) (saddrs (t_D T)).
Proof. intros [[E [HD _]] _]; simpl in HD. rewrite HD. simpl. auto. Qed.

Lemma hca5_PC_pok L P st lic eph reph hash ck ts ri dead lsh valid birth ckb sent mac1 r :
  hca5_pok L P [] -> Zlength eph = 32 -> Zlength reph = 32 -> Zlength hash = 32 -> Zlength ck = 32 ->
  Zlength ts = 12 ->
  hca5_pok L (p_set_refs (p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
                dead lsh valid birth ckb sent mac1) r) [].
Proof.
  intros [Hd [Hs [Hok [Hpk Hsl]]]] H1 H2 H3 H4 H5. unfold hca5_pok, hs_ok in *; simpl.
  intuition.
Qed.

Lemma hca5_PC_ok {Espec: OracleKind} x25519 aead_enc aead_dec xaead_enc xaead_dec (gv: globals) (L: hca5_loc) (FR: mpred) (w: list int64) :
  hca5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hca5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec)
    (hca5_SB x25519 gv L FR w)
    hca5_PC
    (overridePost (hca5_SB x25519 gv L FR w) (hca5_R gv)).
Proof.
  intros HH. unfold hca5_SB, hca5_Delta, hca5_R. abbreviate_semax.
  Intros R S P T.
  unfold hca5_world, hca5_globs, hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
  unfold hca5_PC.
  forward_call (Tsh, l_p L, P, false).
  Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri]; simpl fst in *; simpl snd in *.
  forward_call (Tsh, l_p L, p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri)).
  Intros vret. destruct vret as [[[[[[dead lsh] valid] birth] ckb] sent] mac1]; simpl fst in *; simpl snd in *.
  forward_call tt. Intros r.
  set (P1 := p_rest_randomized (p_set_hs P (hs_randomized (p_hs P) st lic eph reph hash ck ts ri))
               dead lsh valid birth ckb sent mac1).
  rewrite hca5_PC_split. Intros.
  forward.
  sep_apply (hca5_PC_fold Tsh (l_p L) P1 r).
  forward_call tt. Intros b.
  forward_if.
  - forward_call (gv, S, w, Tsh, l_ita L, T, hs_addr (l_p L), @None (share * entry)).
    { change (raw_rep (hs_addr (l_p L)) None) with emp. rewrite emp_sepcon. cancel. }
    { change (raw_ok T (hs_addr (l_p L)) None) with (In (hs_addr (l_p L)) (saddrs (t_D T))).
      apply hca5_PC_raw_ok; auto. }
    change (raw_add T (hs_addr (l_p L)) None) with T. Intros idx.
    Exists R (shim_u32 S idx) (p_set_refs P1 r) (t_insert T (hs_addr (l_p L)) idx).
    unfold hca5_world, hca5_globs, hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
    entailer!.
    split; [apply hca5_PC_pok; auto | apply hca5_PC_pool_insert; auto].
  - forward.
    Exists R S (p_set_refs P1 r) T.
    unfold hca5_world, hca5_globs, hca5_snap0, hca5_scr0, hca5_scr, hca5_lvars; cbn [app].
    entailer!.
    apply hca5_PC_pok; auto.
Qed.
