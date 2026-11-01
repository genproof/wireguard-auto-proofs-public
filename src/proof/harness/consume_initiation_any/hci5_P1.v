(* law consume_initiation_any: main's phase P1, statements 0..8: peers = NULL, the boot clock, wg_noise_init, raw_a / raw_b, setup_device(&wb ..), the two identities, na = hnodes_add(&peers, &wb, ia.pub, 0).
   (states: hci5_defs.v).
   harness/consume_initiation_any/hci3_*.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

#[local] Instance hci5_p1_cceN : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.

Lemma hci5_p1_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_consume_initiation_any sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_initiation_any _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hci5_p1_rest (gv: globals) (S: shim) : mpred :=
  (@data_at Noise.CS Ews tlong (Vlong (s_rsec S)) (gv _wg_shim_real_sec) *
   @data_at Noise.CS Ews tlong (Vlong (s_rnsec S)) (gv _wg_shim_real_nsec) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow))%logic.

Lemma hci5_p1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_consume_initiation_any Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) *
     hci5_p1_rest gv S))%logic.
Proof.
  unfold shim_core, hci5_p1_rest. rewrite <- hci5_p1_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the shim after the first boot clock store *)
Definition hci5_p1_S1 (v: int64) : shim :=
  mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

#[local] Instance hci5_p1_cceH : change_composite_env HCS W_consume_initiation_any.
Proof. make_cs_preserve HCS W_consume_initiation_any. Defined.

#[local] Instance hci5_p1_cceK : change_composite_env CKS W_consume_initiation_any.
Proof. make_cs_preserve CKS W_consume_initiation_any. Defined.

(* nondet_bytes's result as hbytes *)
Lemma hci5_p1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_consume_initiation_any sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_consume_initiation_any _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Section HCSl.
#[local] Existing Instance HCS.

(* m_identity without its pub field *)
Definition hci5_p1_mrest (sh: share) (I: mident) (p: val) : mpred :=
  (field_at sh t_mident (DOT HC._priv) (bytes (mi_priv I)) p *
   field_at sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.

Lemma hci5_p1_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  data_at sh t_mident (mident_val I) p |--
  (hbytes sh (mi_pub I) (offset_val 32 p) * hci5_p1_mrest sh I p)%logic.
Proof.
  intros Hl. unfold hci5_p1_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HC._pub)).
  assert_PROP (field_compatible t_mident (DOT HC._pub) p). { entailer!. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

Lemma hci5_p1_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_pub I) (offset_val 32 p) * hci5_p1_mrest sh I p)%logic |--
  data_at sh t_mident (mident_val I) p.
Proof.
  intros Hl. unfold hci5_p1_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HC._pub)).
  assert_PROP (field_compatible t_mident (DOT HC._priv) p). { entailer!. }
  assert (field_compatible t_mident (DOT HC._pub) p).
  { destruct H as (?&?&?&?&?). repeat split; auto. simpl. unfold in_members. simpl. auto. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

End HCSl.

Section P1.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* A's peer satisfies the invariant *)
Lemma hci5_p1_pok R L p PSK r :
  x25519_props x25519 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 ->
  hci5_pok x25519 R L
    (p, Ews, p_set_refs (setup_peer_val x25519 (hci5_DB x25519 R L) (l_wb L) p nullval
                           (mi_pub (hci5_IA x25519 R)) PSK (Int64.repr 0)) r).
Proof.
  intros Hx Hpsk Hr. unfold hci5_pok; simpl.
  assert (Hp: Zlength (mi_pub (hci5_IA x25519 R)) = 32) by apply Hx.
  repeat split; auto; try (simpl; lia).
  all: try (unfold hs_ok; simpl; repeat split; auto).
  all: try (unfold precomputed; destruct (andb _ _); auto).
Qed.

Lemma hci5_P1_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S0 gv L FR) hci5_P1
    (overridePost (hci5_SA x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH. unfold hci5_S0, hci5_Delta, hci5_R, hci5_P1. simplify_func_tycontext.
  abbreviate_semax.
  unfold hci5_lvars, hci5_snaps0, hci5_scr; cbn [app].
  rewrite shim_state_ex4. Intros w.
  forward. forward_call tt.
  Intros v. unfold shim_state4. rewrite (hci5_p1_core_open gv hci5_shim0). Intros.
  forward. gather_SEP 10 11 12. replace_SEP 0 (shim_state4 gv (hci5_p1_S1 v) w).
  1: unfold shim_state4; rewrite hci5_p1_core_open; entailer!; apply derives_refl.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite !hci5_conv_bytes.
  forward_call (l_rawa L, 32, Tsh). Intros bsa.
  forward_call (l_rawb L, 32, Tsh). Intros bsb.
  rewrite (hci5_p1_nd Tsh 32 bsa) by tauto. rewrite (hci5_p1_nd Tsh 32 bsb) by tauto.
  rewrite <- !hci5_conv_bytes.
  forward_call (gv, hci5_p1_S1 v, w, Tsh, l_wb L, l_itb L, l_ptb L, Tsh, l_rawb L, map Byte.repr bsb).
  { rewrite Zlength_map; tauto. }
  Intros secb.
  unfold hci5_consts. Intros.
  forward_call (gv, Tsh, l_ia L, Tsh, l_rawa L, map Byte.repr bsa).
  1: rewrite Zlength_map; tauto.
  forward_call (gv, Tsh, l_ib L, Tsh, l_rawb L, map Byte.repr bsb).
  1: rewrite Zlength_map; tauto.
  set (R := mkRun5 (map Byte.repr bsa) (map Byte.repr bsb) secb v).
  change (setup_dev x25519 (l_wb L) (l_itb L) (l_ptb L) (map Byte.repr bsb) secb (s_boot (hci5_p1_S1 v)))
    with (hci5_DB x25519 R L).
  change (mident_of x25519 (map Byte.repr bsa)) with (hci5_IA x25519 R).
  change (mident_of x25519 (map Byte.repr bsb)) with (hci5_IB x25519 R).
  assert (HIA: Zlength (mi_pub (hci5_IA x25519 R)) = 32) by (destruct HH as [Hx _]; apply Hx).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  rewrite <- (hci5_conv_hnodep_v Tsh nullval (l_peers L)).
  sep_apply (hci5_p1_mident_split Tsh (hci5_IA x25519 R) (l_ia L) HIA).
  replace_SEP 13 (mem_mgr gv * hnodes_rep4 W nullval [] * peers_rep [])%logic.
  1: entailer!; unfold peers_rep; simpl; entailer!.
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_peers L, nullval, @nil hnode4, @nil (val * share * peer), Tsh, l_wb L,
                hci5_DB x25519 R L, nullval, Tsh, offset_val 32 (l_ia L), mi_pub (hci5_IA x25519 R),
                Int64.repr 0).
  1: constructor.
  Unshelve. all: try exact hci5_p1_cceK.
  Intros vret. destruct vret as [[[na p] PSK] r]. simpl fst in *; simpl snd in *.
  forward.
  assert (HrunR: hci5_run_ok R).
  { unfold hci5_run_ok; simpl. rewrite !Zlength_map. repeat split; auto; lia. }
  change (d_ptab (hci5_DB x25519 R L)) with (l_ptb L).
  destruct (eq_dec na nullval) as [Hn | Hn].
  - (* the add failed: no peer *)
    subst na. repeat flatten_sepcon_in_SEP.
    sep_apply (hci5_p1_mident_join Tsh (hci5_IA x25519 R) (l_ia L) HIA).
    unfold hci5_SA.
    Exists R (shim_draw (hci5_p1_S1 v) secb) w (@nil hnode4) (@nil (val * share * peer)) (mkT [] [])
      nullval nullval.
    unfold hci5_world, hci5_globs, hci5_lvars, hci5_scr, hci5_snaps0, hci5_consts; cbn [app map hci5_head].
    entailer!.
    { unfold hci5_inv, hci5_T_ok, hci5_slots_ok. simpl. repeat split; auto; constructor. }
  - (* A's peer added *)
    destruct (H7 Hn) as [Hpsk Hr].
    destruct HH as [Hx [Ha [Hxa Hrep]]]. destruct Hrep as (_ & _ & _ & _ & Hadd & _).
    repeat flatten_sepcon_in_SEP.
    sep_apply (hci5_p1_mident_join Tsh (hci5_IA x25519 R) (l_ia L) HIA).
    rewrite hci5_conv_hnodep_v.
    sep_apply (Hadd Tsh (l_itb L) (mkT [] []) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
    unfold hci5_SA.
    Exists R (shim_draw (hci5_p1_S1 v) secb) w
      [mkHN4 na p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)]
      [(p, Ews, p_set_refs (setup_peer_val x25519 (hci5_DB x25519 R L) (l_wb L) p nullval
                              (mi_pub (hci5_IA x25519 R)) PSK (Int64.repr 0)) r)]
      (t_add (mkT [] []) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)) p na.
    unfold hci5_world, hci5_globs, hci5_lvars, hci5_scr, hci5_snaps0, hci5_consts; cbn [app hci5_head].
    entailer!.
    unfold hci5_inv. split; [| split; [| split; [| split; [| split; [| split]]]]].
    + constructor; [apply hci5_p1_pok; auto | constructor].
    + constructor; [apply writable_Ews | constructor].
    + simpl. auto.
    + reflexivity.
    + right; simpl; auto.
    + unfold hci5_T_ok, t_entry_d, t_entry; simpl. repeat split; auto.
      constructor; auto. simpl. rewrite if_true by reflexivity. reflexivity.
    + unfold hci5_slots_ok. repeat constructor; auto.
    + apply derives_refl.
Qed.

End P1.
