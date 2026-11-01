(* law handshake: main's phase P1, segment D = statements 21..22: setup_peer x2, the handshake entries into the pools (hhs3_rep's t_add).
   (section P1). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_specs3.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.handshake.hhs3_spec.
Require Import WgNoise.proof.harness.handshake.hhs3_defs.
Require Import WgNoise.proof.harness.handshake.hhs3_conv.
Require Import WgNoise.proof.harness.handshake.hhs3_p1_defs.
Require WgNoise.harness.x_handshake.code.

#[local] Existing Instance W_handshake.
Local Open Scope Z_scope.

Section Seg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* the m_identity struct with its public key apart (setup_peer's pub argument) *)
Definition hhs3D_midrest (sh: share) (p: val) (I: mident) : mpred :=
  (@field_at HCS sh t_mident (DOT HC._priv) (bytes (mi_priv I)) p *
   @field_at HCS sh t_mident (DOT HC._ok) (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.

Lemma hhs3D_mid_split sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (hbytes sh (mi_pub I) (offset_val 32 p) * hhs3D_midrest sh p I)%logic.
Proof.
  intros FC Lpub.
  unfold mident_val. unfold_data_at (@data_at HCS sh t_mident _ p).
  assert (Hpub: @field_at HCS sh t_mident (DOT HC._pub) (bytes (mi_pub I)) p = hbytes sh (mi_pub I) (offset_val 32 p)).
  { rewrite field_at_data_at, field_address_offset by auto with field_compatible. unfold hbytes. rewrite Lpub.
    reflexivity. }
  simpl in Hpub. rewrite Hpub. unfold hhs3D_midrest. apply pred_ext; cancel.
Qed.

Lemma hhs3D_mid_join sh p I :
  @field_compatible HCS t_mident [] p -> Zlength (mi_pub I) = 32 ->
  (hbytes sh (mi_pub I) (offset_val 32 p) * hhs3D_midrest sh p I |-- @data_at HCS sh t_mident (mident_val I) p)%logic.
Proof. intros. rewrite hhs3D_mid_split by auto. cancel. Qed.

Ltac hhs3D_dead :=
  match goal with H: Int.one = Int.zero |- _ => exfalso; exact (Int.one_not_zero H)
             | H: (0 <> 0)%Z |- _ => exfalso; exact (H eq_refl) end.

Lemma hhs3D_tadd a E : t_add (mkT [] []) a Tsh E = mkT [(a, Tsh, E)] [].
Proof. reflexivity. Qed.

Lemma hhs3_p1_D_ok {Espec: OracleKind} gv L FR :
  hhs3_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hhs3_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hhs3_p1_SB x25519 gv L FR) hhs3_p1_D
    (overridePost (hhs3_p1_SD x25519 gv L FR) (hhs3_R gv)).
Proof.
  intros HH. unfold hhs3_p1_SB, hhs3_Delta, hhs3_R, hhs3_p1_D. simplify_func_tycontext. abbreviate_semax.
  Intros R S a0 f0 l0.
  unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
  destruct HH as (Hx & _ & _ & _ & Hrep). pose proof H as (La & Lb & Lpsk & Hup & _).
  assert (LQa: Zlength (mi_pub (hhs3_IA x25519 R)) = 32) by apply Hx.
  assert (LQb: Zlength (mi_pub (hhs3_IB x25519 R)) = 32) by apply Hx.
  assert_PROP (@field_compatible HCS t_mident [] (l_ia L) /\ @field_compatible HCS t_mident [] (l_ib L) /\
               isptr (l_psk L)) as FCi by entailer!.
  destruct FCi as (FCia & FCib & Ppsk).
  rewrite (hhs3D_mid_split Tsh (l_ia L)) by auto. rewrite (hhs3D_mid_split Tsh (l_ib L)) by auto.
  Intros.
  assert (NN: l_psk L <> nullval) by (destruct (l_psk L); try contradiction; discriminate).
  destruct (r_up R) eqn:UP.
  - apply -> seq_assoc. apply semax_if_seq. forward_if; [ | hhs3D_dead].
    forward.
    forward_call (gv, Tsh, l_pb L, Tsh, l_wa L, hhs3_DA x25519 R L, nullval, Tsh, offset_val 32 (l_ib L),
                  mi_pub (hhs3_IB x25519 R), l_psk L, r_psk R, Int64.repr 1).
    { destruct (eq_dec (l_psk L) nullval); [congruence | cancel]. }
    destruct (eq_dec (l_psk L) nullval) as [E|_]; [congruence | ].
    apply semax_if_seq. forward_if; [ | hhs3D_dead].
    forward.
    forward_call (gv, Tsh, l_pa L, Tsh, l_wb L, hhs3_DB x25519 R L, nullval, Tsh, offset_val 32 (l_ia L),
                  mi_pub (hhs3_IA x25519 R), l_psk L, r_psk R, Int64.repr 2).
    { destruct (eq_dec (l_psk L) nullval); [congruence | cancel]. }
    destruct (eq_dec (l_psk L) nullval) as [E|_]; [congruence | ].
    destruct Hrep as (_ & _ & _ & _ & Hadd & _).
    sep_apply (Hadd Tsh (l_ita L) (mkT [] []) (hs_addr (l_pb L)) Tsh (mkEntry (l_pb L) IDX_HANDSHAKE Int.zero)
                 writable_share_top).
    sep_apply (Hadd Tsh (l_itb L) (mkT [] []) (hs_addr (l_pa L)) Tsh (mkEntry (l_pa L) IDX_HANDSHAKE Int.zero)
                 writable_share_top).
    rewrite !hhs3D_tadd.
    sep_apply (hhs3D_mid_join Tsh (l_ia L) (hhs3_IA x25519 R) FCia LQa).
    sep_apply (hhs3D_mid_join Tsh (l_ib L) (hhs3_IB x25519 R) FCib LQb).
    change (d_ptab (hhs3_DA x25519 R L)) with (l_pta L). change (d_ptab (hhs3_DB x25519 R L)) with (l_ptb L).
    change (setup_peer_val x25519 (hhs3_DA x25519 R L) (l_wa L) (l_pb L) nullval (mi_pub (hhs3_IB x25519 R))
              (r_psk R) (Int64.repr 1)) with (hhs3_PB0 x25519 R L).
    change (setup_peer_val x25519 (hhs3_DB x25519 R L) (l_wb L) (l_pa L) nullval (mi_pub (hhs3_IA x25519 R))
              (r_psk R) (Int64.repr 2)) with (hhs3_PA0 x25519 R L).
    change (mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE Int.zero)] []) with (hhs3_TA0 L).
    change (mkT [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE Int.zero)] []) with (hhs3_TB0 L).
    unfold hhs3_p1_SD. Exists R S a0 f0 l0.
    unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
    entailer!.
  - apply -> seq_assoc. apply semax_if_seq. forward_if; [hhs3D_dead | ].
    forward.
    forward_call (gv, Tsh, l_pb L, Tsh, l_wa L, hhs3_DA x25519 R L, nullval, Tsh, offset_val 32 (l_ib L),
                  mi_pub (hhs3_IB x25519 R), nullval, r_psk R, Int64.repr 1).
    { rewrite if_true by auto. cancel. }
    rewrite if_true by auto.
    apply semax_if_seq. forward_if; [hhs3D_dead | ].
    forward.
    forward_call (gv, Tsh, l_pa L, Tsh, l_wb L, hhs3_DB x25519 R L, nullval, Tsh, offset_val 32 (l_ia L),
                  mi_pub (hhs3_IA x25519 R), nullval, r_psk R, Int64.repr 2).
    rewrite !if_true by auto. rewrite <- (Hup eq_refl).
    destruct Hrep as (_ & _ & _ & _ & Hadd & _).
    sep_apply (Hadd Tsh (l_ita L) (mkT [] []) (hs_addr (l_pb L)) Tsh (mkEntry (l_pb L) IDX_HANDSHAKE Int.zero)
                 writable_share_top).
    sep_apply (Hadd Tsh (l_itb L) (mkT [] []) (hs_addr (l_pa L)) Tsh (mkEntry (l_pa L) IDX_HANDSHAKE Int.zero)
                 writable_share_top).
    rewrite !hhs3D_tadd.
    sep_apply (hhs3D_mid_join Tsh (l_ia L) (hhs3_IA x25519 R) FCia LQa).
    sep_apply (hhs3D_mid_join Tsh (l_ib L) (hhs3_IB x25519 R) FCib LQb).
    change (d_ptab (hhs3_DA x25519 R L)) with (l_pta L). change (d_ptab (hhs3_DB x25519 R L)) with (l_ptb L).
    change (setup_peer_val x25519 (hhs3_DA x25519 R L) (l_wa L) (l_pb L) nullval (mi_pub (hhs3_IB x25519 R))
              (r_psk R) (Int64.repr 1)) with (hhs3_PB0 x25519 R L).
    change (setup_peer_val x25519 (hhs3_DB x25519 R L) (l_wb L) (l_pa L) nullval (mi_pub (hhs3_IA x25519 R))
              (r_psk R) (Int64.repr 2)) with (hhs3_PA0 x25519 R L).
    change (mkT [(hs_addr (l_pb L), Tsh, mkEntry (l_pb L) IDX_HANDSHAKE Int.zero)] []) with (hhs3_TA0 L).
    change (mkT [(hs_addr (l_pa L), Tsh, mkEntry (l_pa L) IDX_HANDSHAKE Int.zero)] []) with (hhs3_TB0 L).
    unfold hhs3_p1_SD. Exists R S a0 f0 l0.
    unfold hhs3_globs, hhs3_cnt_temps, hhs3_lvars, hhs3_p1_rest, hhs3_scr_tmp; cbn [app].
    entailer!.
Qed.

End Seg.
