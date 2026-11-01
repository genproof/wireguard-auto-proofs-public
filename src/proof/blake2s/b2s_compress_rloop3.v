(* blake2s_compress_generic: the loop over the 10 rounds. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog3.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stmts.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_round3.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_rloop_ok {Espec: OracleKind} mw v0 vv vm ctx data nb inc gv FR :
  Zlength mw = 16 -> Zlength v0 = 16 ->
  semax b2s_cDelta
    (PROP ()
     LOCAL (lvar code._v (tarray tuint 16) vv; lvar code._m (tarray tuint 16) vm; gvars gv;
            temp code._ctx ctx; temp code._data data; temp code._nblocks nb; temp code._inc inc)
     SEP (data_at Tsh (tarray tuint 16) (map Vint v0) vv;
          data_at Tsh (tarray tuint 16) (map Vint mw) vm; blake2s_globals gv; FR))
    b2s_rloop_stmt
    (normal_ret_assert
    (PROP ()
     LOCAL (temp code._r (Vint (Int.repr 10));
            lvar code._v (tarray tuint 16) vv; lvar code._m (tarray tuint 16) vm; gvars gv;
            temp code._ctx ctx; temp code._data data; temp code._nblocks nb; temp code._inc inc)
     SEP (data_at Tsh (tarray tuint 16) (map Vint (b2s_rounds mw v0 10)) vv;
          data_at Tsh (tarray tuint 16) (map Vint mw) vm; blake2s_globals gv; FR))).
Proof.
intros Hmw Hv0.
unfold b2s_rloop_stmt. abbreviate_semax.
assert (E0: b2s_rounds mw v0 0 = v0) by reflexivity.
rewrite <- E0.
forward_for_simple_bound 10 (EX r: Z,
  PROP ()
  LOCAL (lvar code._v (tarray tuint 16) vv; lvar code._m (tarray tuint 16) vm; gvars gv;
         temp code._ctx ctx; temp code._data data; temp code._nblocks nb; temp code._inc inc)
  SEP (data_at Tsh (tarray tuint 16) (map Vint (b2s_rounds mw v0 r)) vv;
       data_at Tsh (tarray tuint 16) (map Vint mw) vm; blake2s_globals gv; FR))%assert.
{ entailer!. }
{ cbv beta.
  eapply semax_pre; [ | eapply semax_post; [ | | | |
      apply (b2s_round_ok i mw vv vm ctx data nb inc gv FR (b2s_rounds mw v0 i)) ] ].
  { unfold b2s_rstate. entailer!. }
  { unfold POSTCONDITION, abbreviate. simpl_ret_assert. rewrite <- b2s_rounds_succ by lia.
    unfold b2s_rstate. entailer!. }
  { unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
  { unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
  { intros. unfold POSTCONDITION, abbreviate. simpl_ret_assert. normalize. }
  { lia. }
  { auto. }
  { rewrite b2s_Zlength_rounds; auto. } }
entailer!.
Qed.
