(* law config_any: main's phase P5a, statements 43..56: step 5: q's handshake fields ANY, hs_randomize(&q.handshake), qpub, psk, use_psk, wg_noise_handshake_init(&q.handshake, &w.static_identity, qpub, use_psk ? psk : NULL, &q).
   (states: hcf5_defs.v).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_cut.
Require Import WgNoise.proof.harness.config_any.hcf5_globals.
Require Import WgNoise.proof.harness.config_any.hcf5_spec.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_conv.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.
Require Import WgNoise.proof.harness.config_any.hcf5_p5a_lem.

#[local] Existing Instance W_config_any.
Local Open Scope Z_scope.

Ltac hcf5_p5a_shut X :=
  gather_SEP 0 1; replace_SEP 0 X;
  [go_lowerx; rewrite sepcon_emp;
   eapply derives_trans; [apply sepcon_derives; [apply derives_refl | eapply allp_left; apply derives_refl] |];
   apply wand_frame_elim |].

Ltac hcf5_p5a_bt :=
  forward; match goal with Hn: Int.and _ _ <> Int.zero |- _ => rewrite (Int.eq_false _ _ Hn) end; entailer!.
Ltac hcf5_p5a_bf :=
  forward; match goal with Hn: Int.and _ _ = Int.zero |- _ => rewrite Hn, Int.eq_true end; entailer!.

Section P5a.
Variable x25519: list byte -> list byte -> list byte.

Lemma hcf5_P5a_ok {Espec: OracleKind} gv L FR :
  hcf5_hyps x25519 -> hcf5_sepH ->
  semax (hcf5_Delta x25519) (hcf5_SX1 x25519 gv L FR) hcf5_P5a
    (overridePost (hcf5_S5a x25519 gv L FR) (hcf5_R gv)).
Proof.
  intros HX HS. unfold hcf5_SX1, hcf5_F, hcf5_Fx.
  Intros R S w D P T KE D0. Intros sn0 P0 r0 S0 w0 h0 RAW.
  unfold hcf5_P5a.
  unfold hcf5_core, hcf5_globs, hcf5_X1, hcf5_lvars. cbn [app].
  repeat flatten_sepcon_in_SEP.
  rewrite (proj1 HS (l_q L)).
  repeat flatten_sepcon_in_SEP.
  assert_PROP (@field_compatible Noise.CS t_peer [StructField I._device] (l_q L)) as Hfq0
    by (go_lowerx; saturate_local; apply prop_right; assumption).
  assert (Hfq: @field_compatible Noise.CS t_peer [] (l_q L))
    by (destruct Hfq0 as (? & ? & ? & ? & ? & ?); repeat split; auto).
  clear Hfq0.
  freeze [1;2;3;4;5;6;7;8;9;10;11;12;13;15;16;17;18;19;20;21;23;24] FZ.
  unfold hcf5_Delta. simplify_func_tycontext. abbreviate_semax.
  forward_call tt. Intros b1.
  forward_if (temp HF5._t'51 (if Int.eq (Int.and (Int.repr b1) (Int.repr 1)) Int.zero then nullval else l_p L)).
  { hcf5_p5a_bt. }
  { hcf5_p5a_bf. }
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._peer; StructField I._entry]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* entry.next *)
  forward_call tt. Intros b2.
  forward_if (temp HF5._t'53 (if Int.eq (Int.and (Int.repr b2) (Int.repr 1)) Int.zero then nullval
                              else offset_val 48 (l_p L))).
  { hcf5_p5a_bt. unfold eval_field; simpl. rewrite offset_offset_val. reflexivity. }
  { hcf5_p5a_bf. }
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._next; StructField I._entry]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* entry.hashed *)
  forward_call tt. Intros b3.
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._hashed; StructField I._entry]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* entry.type *)
  forward_call tt. Intros b4.
  forward_if (temp HF5._t'56 (Vint (if Int.eq (Int.and (Int.repr b4) (Int.repr 1)) Int.zero then Int.repr 2
                                    else Int.repr 1))).
  { hcf5_p5a_bt. }
  { hcf5_p5a_bf. }
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._type; StructField I._entry]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* entry.index *)
  forward_call tt. Intros n5.
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._index; StructField I._entry]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* static_identity *)
  forward_call tt. Intros b6.
  forward_if (temp HF5._t'59 (if Int.eq (Int.and (Int.repr b6) (Int.repr 1)) Int.zero then nullval
                              else offset_val 8 (l_w L))).
  { hcf5_p5a_bt. }
  { hcf5_p5a_bf. }
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._static_identity]).
  { compute; tauto. }
  simpl app. flatten_sepcon_in_SEP.
  forward.
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* the three byte arrays *)
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._remote_static]).
  { compute; tauto. }
  rewrite (hcf5_p5a_rs_ _ Hfq). flatten_sepcon_in_SEP.
  forward_call (offset_val 136 (l_q L), 32, Tsh). Intros bs7.
  rewrite <- (hcf5_p5a_rs _ _ Hfq).
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._precomputed_static_static]).
  { compute; tauto. }
  rewrite (hcf5_p5a_ss_ _ Hfq). flatten_sepcon_in_SEP.
  forward_call (offset_val 200 (l_q L), 32, Tsh). Intros bs8.
  rewrite <- (hcf5_p5a_ss _ _ Hfq).
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  sep_apply (hcf5_p5a_open (l_q L) [StructField I._preshared_key]).
  { compute; tauto. }
  rewrite (hcf5_p5a_psk_ _ Hfq). flatten_sepcon_in_SEP.
  forward_call (offset_val 232 (l_q L), 32, Tsh). Intros bs9.
  rewrite <- (hcf5_p5a_psk _ _ Hfq).
  hcf5_p5a_shut (@data_at_ Noise.CS Tsh t_hs (hs_addr (l_q L))).
  (* hs_randomize(&q.handshake) over any memory *)
  forward_call (Tsh, l_q L, P, true).
  Intros vret.
  (* qpub, psk, use_psk *)
  rewrite !hcf5_conv_bytes.
  forward_call (l_qpub L, 32, Tsh). Intros bq.
  forward_call (l_psk L, 32, Tsh). Intros bk.
  forward_call tt. Intros bu.
  forward.
  rewrite (hcf5_p5a_nd Tsh bq) by assumption. rewrite (hcf5_p5a_nd Tsh bk) by assumption.
  rewrite hcf5_p5a_and1.
  rewrite hcf5_p5a_dev_split. flatten_sepcon_in_SEP.
  destruct (Int.eq (Int.and (Int.repr bu) (Int.repr 1)) Int.zero) eqn:Eu.
  - forward_if (temp HF5._t'61 nullval).
    { exfalso. auto. }
    { forward. entailer!. }
    forward_call (gv, Tsh, l_q L, Tsh, id_addr (l_w L), d_id D, Tsh, l_qpub L, map Byte.repr bq, Tsh, nullval,
                  map Byte.repr bk).
    { destruct (eq_dec nullval nullval) as [_ | C]; [| congruence]. cancel. }
    { rewrite Zlength_map; assumption. }
    destruct (eq_dec nullval nullval) as [_ | C]; [| congruence].
    thaw FZ.
    assert_PROP (itable_wf T) as Hwf by (unfold itable; go_lowerx; normalize; apply prop_right; assumption).
    sep_apply (prot_rep3_pool_add Tsh (l_it L) T (hs_addr (l_q L)) Tsh
                 (mkEntry (l_q L) IDX_HANDSHAKE Int.zero) writable_share_top).
    set (T' := t_add T (hs_addr (l_q L)) Tsh (mkEntry (l_q L) IDX_HANDSHAKE Int.zero)).
    assert_PROP (itable_wf T') as Hwf' by (unfold itable; go_lowerx; normalize; apply prop_right; assumption).
    assert (Hn: ~ In (hs_addr (l_q L)) (saddrs (t_D T))).
    { destruct Hwf' as (_ & _ & Hnd & _). unfold T', t_add in Hnd. simpl in Hnd. inversion Hnd; assumption. }
    pose proof (hcf5_p5a_inv _ _ _ _ _ _ _ _ H0 Hwf Hn) as Hinv.
    pose proof (hcf5_p5a_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 (hs_addr (l_q L)) Tsh (mkEntry (l_q L) IDX_HANDSHAKE Int.zero)
                  (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))) Hn H1) as Hsame.
    fold T' in Hinv, Hsame.
    unfold hcf5_S5a.
    Exists R S w D P T' KE D0. Exists sn0 P0 r0 S0. Exists w0 h0 RAW (map Byte.repr bq). Exists (map Byte.repr bk) false.
    unfold hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X5a, hcf5_lvars, hcf5_qhs, hs_mem. cbn [app].
    rewrite <- !hcf5_p5a_bh, hcf5_p5a_dev_split. simpl (p_hs _).
    clear - Hinv Hsame H H21 H23.
    entailer!.
    split; rewrite Zlength_map; assumption.
  - forward_if (temp HF5._t'61 (l_psk L)).
    { forward. entailer!. }
    { exfalso. match goal with Hc: Int.one = Int.zero |- _ => discriminate Hc end. }
    assert_PROP (isptr (l_psk L)) as Hpk by entailer!.
    forward_call (gv, Tsh, l_q L, Tsh, id_addr (l_w L), d_id D, Tsh, l_qpub L, map Byte.repr bq, Tsh, l_psk L,
                  map Byte.repr bk).
    { destruct (eq_dec (l_psk L) nullval) as [C | _]; [rewrite C in Hpk; contradiction |]. cancel. }
    { split; [| intros _]; rewrite Zlength_map; assumption. }
    destruct (eq_dec (l_psk L) nullval) as [C | _]; [rewrite C in Hpk; contradiction |].
    thaw FZ.
    assert_PROP (itable_wf T) as Hwf by (unfold itable; go_lowerx; normalize; apply prop_right; assumption).
    sep_apply (prot_rep3_pool_add Tsh (l_it L) T (hs_addr (l_q L)) Tsh
                 (mkEntry (l_q L) IDX_HANDSHAKE Int.zero) writable_share_top).
    set (T' := t_add T (hs_addr (l_q L)) Tsh (mkEntry (l_q L) IDX_HANDSHAKE Int.zero)).
    assert_PROP (itable_wf T') as Hwf' by (unfold itable; go_lowerx; normalize; apply prop_right; assumption).
    assert (Hn: ~ In (hs_addr (l_q L)) (saddrs (t_D T))).
    { destruct Hwf' as (_ & _ & Hnd & _). unfold T', t_add in Hnd. simpl in Hnd. inversion Hnd; assumption. }
    pose proof (hcf5_p5a_inv _ _ _ _ _ _ _ _ H0 Hwf Hn) as Hinv.
    pose proof (hcf5_p5a_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 (hs_addr (l_q L)) Tsh (mkEntry (l_q L) IDX_HANDSHAKE Int.zero)
                  (proj1 (proj2 (proj2 (proj2 (proj2 (proj2 (proj2 H0))))))) Hn H1) as Hsame.
    fold T' in Hinv, Hsame.
    unfold hcf5_S5a.
    Exists R S w D P T' KE D0. Exists sn0 P0 r0 S0. Exists w0 h0 RAW (map Byte.repr bq). Exists (map Byte.repr bk) true.
    unfold hcf5_Fx, hcf5_core, hcf5_globs, hcf5_X5a, hcf5_lvars, hcf5_qhs, hs_mem. cbn [app].
    rewrite <- !hcf5_p5a_bh, hcf5_p5a_dev_split. simpl (p_hs _).
    clear - Hinv Hsame H H21 H23.
    entailer!.
    split; rewrite Zlength_map; assumption.
Qed.

End P5a.
