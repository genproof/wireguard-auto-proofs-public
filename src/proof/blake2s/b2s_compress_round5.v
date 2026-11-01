(* blake2s_compress_generic: one round (the eight G macros) as one semax lemma, in the context b2s_Gprog5. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_G5.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_round5_ok {Espec: OracleKind} r m vv vm ctx data nb inc gv FR v :
  0 <= r < 10 -> Zlength m = 16 -> Zlength v = 16 ->
  semax b2s_cDelta5 (b2s_rstate r v m vv vm ctx data nb inc gv FR) b2s_round_stmt
    (normal_ret_assert
       (b2s_rstate r (b2s_round m v (Znth r b2s_sigma)) m vv vm ctx data nb inc gv FR)).
Proof.
  intros Hr Hm Hv. rewrite b2s_round_stmt_eq.
  eapply semax_seq'. { apply b2s_G5_ok_1; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_2; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_3; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_4; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_5; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_6; auto. rewrite !b2s_Zlength_G; auto. }
  eapply semax_seq'. { apply b2s_G5_ok_7; auto. rewrite !b2s_Zlength_G; auto. }
  unfold b2s_round. cbv zeta beta.
  apply b2s_G5_ok_8; auto. rewrite !b2s_Zlength_G; auto.
Qed.
