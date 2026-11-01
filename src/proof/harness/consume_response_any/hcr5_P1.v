(* law consume_response_any, phase P1: statements 0..8 of main: peers = NULL, the boot clock, wg_noise_init, raw_a / raw_b, setup_device, the identities, nb = hnodes_add(&peers, &wa, ib.pub, 0).
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_cut.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_model.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_spec.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_defs.
Require Import WgNoise.proof.harness.consume_response_any.hcr5_conv.
Require WgNoise.harness.x_consume_response_any.code.

#[local] Existing Instance W_consume_response_any.
Local Open Scope logic.

Local Open Scope Z_scope.

#[local] Instance hcr5_p1_cceN : change_composite_env Noise.CS W_consume_response_any.
Proof. make_cs_preserve Noise.CS W_consume_response_any. Defined.

Lemma hcr5_p1_tulong_cs sh v p :
  @data_at Noise.CS sh tulong v p = @data_at W_consume_response_any sh tulong v p.
Proof.
  rewrite (@data_at_change_composite Noise.CS W_consume_response_any _ sh tulong v v (JMeq_refl v));
    [reflexivity | prove_cs_preserve_type].
Qed.

Definition hcr5_p1_rest (gv: globals) (S: shim) : mpred :=
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

Lemma hcr5_p1_core_open gv S :
  shim_core gv S = (!! shim_ok S &&
    (@data_at W_consume_response_any Ews tulong (Vlong (s_boot S)) (gv HC._wg_shim_boottime_ns) *
     hcr5_p1_rest gv S))%logic.
Proof.
  unfold shim_core, hcr5_p1_rest. rewrite <- hcr5_p1_tulong_cs. rewrite !sepcon_assoc. reflexivity.
Qed.

(* the shim after the first boot clock store *)
Definition hcr5_p1_S1 (v: int64) : shim :=
  mkShim v Int64.zero Int64.zero zeros32 zeros32 Int.zero Int64.zero Int64.zero Int64.zero false
         Int64.zero false.

#[local] Instance hcr5_p1_cceH : change_composite_env HCS W_consume_response_any.
Proof. make_cs_preserve HCS W_consume_response_any. Defined.

#[local] Instance hcr5_p1_cceK : change_composite_env CKS W_consume_response_any.
Proof. make_cs_preserve CKS W_consume_response_any. Defined.

(* nondet_bytes's result as hbytes *)
Lemma hcr5_p1_nd sh n bs p : Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_consume_response_any sh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p =
  hbytes sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. subst n. unfold hbytes, bytes. rewrite Zlength_map.
  rewrite (@data_at_change_composite HCS W_consume_response_any _ sh (tarray tuchar (Zlength bs))
             (map Vubyte (map Byte.repr bs)) (map Vubyte (map Byte.repr bs)) (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. rewrite map_map. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Section HCSl.
#[local] Existing Instance HCS.

(* m_identity without its pub field *)
Definition hcr5_p1_mrest (sh: share) (I: mident) (p: val) : mpred :=
  (field_at sh t_mident (DOT HC._priv) (bytes (mi_priv I)) p *
   field_at sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.

Lemma hcr5_p1_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  data_at sh t_mident (mident_val I) p |--
  (hbytes sh (mi_pub I) (offset_val 32 p) * hcr5_p1_mrest sh I p)%logic.
Proof.
  intros Hl. unfold hcr5_p1_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HC._pub)).
  assert_PROP (field_compatible t_mident (DOT HC._pub) p). { entailer!. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

Lemma hcr5_p1_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_pub I) (offset_val 32 p) * hcr5_p1_mrest sh I p)%logic |--
  data_at sh t_mident (mident_val I) p.
Proof.
  intros Hl. unfold hcr5_p1_mrest, hbytes. rewrite Hl.
  unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident (DOT HC._pub)).
  assert_PROP (field_compatible t_mident (DOT HC._priv) p). { entailer!. }
  assert (field_compatible t_mident (DOT HC._pub) p).
  { destruct H as (?&?&?&?&?). repeat split; auto. simpl. unfold in_members. simpl. auto. }
  unfold field_address; rewrite if_true by auto. simpl. cancel.
Qed.

End HCSl.

Section Phase.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* B's peer satisfies the invariant *)
Lemma hcr5_p1_pok R L p PSK r :
  x25519_props x25519 -> Zlength PSK = 32 -> 0 < Int.unsigned r < 2147483647 -> isptr p ->
  hcr5_pok L []
    (p, Ews, p_set_refs (setup_peer_val x25519 (hcr5_DAL x25519 R L) (l_wa L) p nullval
                           (mi_pub (hcr5_IB x25519 R)) PSK (Int64.repr 0)) r).
Proof.
  intros Hx Hpsk Hr Hp. unfold hcr5_pok; simpl.
  assert (Hq: Zlength (mi_pub (hcr5_IB x25519 R)) = 32) by apply Hx.
  repeat split; auto; try (simpl; lia).
  all: try (unfold hs_ok; simpl; repeat split; auto).
  all: try (unfold precomputed; destruct (andb _ _); auto).
  all: try apply Hx.
  all: repeat constructor; auto.
Qed.

Lemma hcr5_P1_ok {Espec: OracleKind} gv L FR :
  hcr5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec -> 
  semax (hcr5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hcr5_S0 gv L FR) hcr5_P1
    (overridePost (hcr5_SA x25519 gv L FR) (hcr5_R gv)).
Proof.
  intros HH. unfold hcr5_S0, hcr5_Delta, hcr5_R, hcr5_P1. simplify_func_tycontext.
  abbreviate_semax.
  unfold hcr5_lvars, hcr5_snaps0, hcr5_scr; cbn [app].
  forward. forward_call tt.
  Intros v. unfold shim_state4. rewrite (hcr5_p1_core_open gv hcr5_shim0). Intros.
  forward. gather_SEP 10 11 12. replace_SEP 0 (shim_state4 gv (hcr5_p1_S1 v) hcr5_w0).
  1: unfold shim_state4; rewrite hcr5_p1_core_open; entailer!; apply derives_refl.
  forward_call (gv, zeros32, zeros32, Int64.zero).
  rewrite !hcr5_conv_bytes.
  forward_call (l_rawa L, 32, Tsh). Intros bsa.
  forward_call (l_rawb L, 32, Tsh). Intros bsb.
  rewrite (hcr5_p1_nd Tsh 32 bsa) by tauto. rewrite (hcr5_p1_nd Tsh 32 bsb) by tauto.
  rewrite <- !hcr5_conv_bytes.
  forward_call (gv, hcr5_p1_S1 v, hcr5_w0, Tsh, l_wa L, l_ita L, l_pta L, Tsh, l_rawa L, map Byte.repr bsa).
  { rewrite Zlength_map; tauto. }
  Intros seca.
  unfold hcr5_consts. Intros.
  forward_call (gv, Tsh, l_ia L, Tsh, l_rawa L, map Byte.repr bsa).
  1: rewrite Zlength_map; tauto.
  forward_call (gv, Tsh, l_ib L, Tsh, l_rawb L, map Byte.repr bsb).
  1: rewrite Zlength_map; tauto.
  set (R := mkRun5 (map Byte.repr bsa) (map Byte.repr bsb) seca v).
  change (setup_dev x25519 (l_wa L) (l_ita L) (l_pta L) (map Byte.repr bsa) seca (s_boot (hcr5_p1_S1 v)))
    with (hcr5_DAL x25519 R L).
  change (mident_of x25519 (map Byte.repr bsa)) with (hcr5_IA x25519 R).
  change (mident_of x25519 (map Byte.repr bsb)) with (hcr5_IB x25519 R).
  assert (HIB: Zlength (mi_pub (hcr5_IB x25519 R)) = 32) by (destruct HH as [Hx _]; apply Hx).
  change (Vlong (Int64.repr (Int.signed (Int.repr 0)))) with nullval.
  rewrite <- (hcr5_conv_hnodep_v Tsh nullval (l_peers L)).
  sep_apply (hcr5_p1_mident_split Tsh (hcr5_IB x25519 R) (l_ib L) HIB).
  replace_SEP 13 (mem_mgr gv * hnodes_rep4 W nullval [] * peers_rep [])%logic.
  1: entailer!; unfold peers_rep; simpl; entailer!.
  repeat flatten_sepcon_in_SEP.
  forward_call (gv, Tsh, l_peers L, nullval, @nil hnode4, @nil (val * share * peer), Tsh, l_wa L,
                hcr5_DAL x25519 R L, nullval, Tsh, offset_val 32 (l_ib L), mi_pub (hcr5_IB x25519 R),
                Int64.repr 0).
  1: constructor.
  Unshelve. all: try exact hcr5_p1_cceK.
  Intros vret. destruct vret as [[[nb p] PSK] r]. simpl fst in *; simpl snd in *.
  forward.
  assert (HrunR: hcr5_run_ok R).
  { unfold hcr5_run_ok; simpl. rewrite !Zlength_map. repeat split; auto; lia. }
  change (d_ptab (hcr5_DAL x25519 R L)) with (l_pta L).
  destruct (eq_dec nb nullval) as [Hn | Hn].
  - (* the add failed: no peer *)
    subst nb. repeat flatten_sepcon_in_SEP.
    sep_apply (hcr5_p1_mident_join Tsh (hcr5_IB x25519 R) (l_ib L) HIB).
    unfold hcr5_SA.
    Exists R (shim_draw (hcr5_p1_S1 v) seca) (@nil hnode4) (@nil (val * share * peer)) nullval nullval
      (mkT [] []).
    unfold hcr5_world, hcr5_globs, hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_consts; cbn [app map hcr5_head].
    entailer!.
    { split.
      - unfold hcr5_list_ok. repeat split; auto; constructor.
      - unfold hcr5_pool. simpl. split; constructor. }
  - (* B's peer added *)
    destruct (H7 Hn) as [Hpsk Hr].
    destruct HH as [Hx [Ha [Hxa Hrep]]]. destruct Hrep as (_ & _ & _ & _ & Hadd & _).
    repeat flatten_sepcon_in_SEP.
    sep_apply (hcr5_p1_mident_join Tsh (hcr5_IB x25519 R) (l_ib L) HIB).
    assert_PROP (isptr p) as Hpp.
    { unfold peers_rep; simpl iter_sepcon. unfold peer_rep. Intros. entailer!.
      match goal with H: field_compatible t_peer [] p |- _ => destruct H as [? _]; assumption end. }
    rewrite hcr5_conv_hnodep_v.
    sep_apply (Hadd Tsh (l_ita L) (mkT [] []) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero) writable_Ews).
    unfold hcr5_SA.
    Exists R (shim_draw (hcr5_p1_S1 v) seca)
      [mkHN4 nb p (@default_val CKS t_hsnap) Vundef (@default_val CKS t_prsnap)]
      [(p, Ews, p_set_refs (setup_peer_val x25519 (hcr5_DAL x25519 R L) (l_wa L) p nullval
                              (mi_pub (hcr5_IB x25519 R)) PSK (Int64.repr 0)) r)] p nb
      (t_add (mkT [] []) (hs_addr p) Ews (mkEntry p IDX_HANDSHAKE Int.zero)).
    unfold hcr5_world, hcr5_globs, hcr5_lvars, hcr5_scr, hcr5_snaps0, hcr5_consts; cbn [app hcr5_head].
    entailer!.
    2: apply derives_refl.
    split.
    + unfold hcr5_list_ok. split; [| split; [| split; [| split; [| split]]]].
      * constructor; [apply hcr5_p1_pok; auto | constructor].
      * constructor; [apply writable_Ews | constructor].
      * simpl. auto.
      * reflexivity.
      * simpl. constructor; [intros [] | constructor].
      * right; simpl; auto.
    + unfold hcr5_pool. simpl. split; [constructor |].
      constructor; [simpl; auto | constructor].
Qed.

End Phase.
