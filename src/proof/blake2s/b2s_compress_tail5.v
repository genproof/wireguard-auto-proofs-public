(* blake2s_compress_generic: the rounds and the feed-forward of one block, in the context b2s_Gprog5. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.blake2s.b2s_prog5.
Require WgNoise.blake2s.code.
Require Import WgNoise.proof.blake2s.b2s_compress_stepstmt.
Require Import WgNoise.proof.blake2s.b2s_compress_prestmt.
Require Import WgNoise.proof.blake2s.b2s_compress_facts.
Require Import WgNoise.proof.blake2s.b2s_compress_G3.
Require Import WgNoise.proof.blake2s.b2s_compress_tail3.
Require Import WgNoise.proof.blake2s.b2s_compress_G5.
Require Import WgNoise.proof.blake2s.b2s_compress_rloop5.
Require Import WgNoise.proof.blake2s.b2s_compress_feed5.

#[local] Existing Instance Blake2s.CS.
Local Open Scope Z_scope.

Lemma b2s_tail5_ok {Espec: OracleKind} sh ctx h t f0 dsh data n inc bs gv v_m v_v k :
  writable_share sh -> Zlength h = 8 -> 0 <= n -> Zlength bs = 64 * n -> 0 < n - k -> 0 <= k <= n ->
  semax b2s_cDelta5
  (PROP ()
   LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
          temp code._ctx ctx; temp code._data (offset_val (64 * k) data);
          temp code._nblocks (Vlong (Int64.repr (n - k))); temp code._inc (Vint (Int.repr inc)))
   SEP (data_at Tsh (tarray tuint 16)
          (map Vint (b2s_v0 (b2s_compress_n (Z.to_nat k) h t f0 inc bs) (b2s_t0 (t + k * inc + inc))
                       (b2s_t1 (t + k * inc + inc)) f0 Int.zero)) v_v;
        data_at Tsh (tarray tuint 16) (map Vint (b2s_words (sublist (64 * k) (64 * k + 64) bs))) v_m;
        blake2s_globals gv;
        field_at sh t_blake2s_ctx (DOT _t)
          [Vint (b2s_t0 (t + k * inc + inc)); Vint (b2s_t1 (t + k * inc + inc))] ctx;
        field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat k) h t f0 inc bs)) ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
        data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data))%assert
  (Ssequence b2s_rloop_stmt b2s_feed_stmt)
  (normal_ret_assert
  (EX a: Z,
   PROP (0 <= a <= n)
   LOCAL (lvar code._v (tarray tuint 16) v_v; lvar code._m (tarray tuint 16) v_m; gvars gv;
          temp code._ctx ctx; temp code._data (offset_val (64 * a) data);
          temp code._nblocks (Vlong (Int64.repr (n - a))); temp code._inc (Vint (Int.repr inc)))
   SEP (data_at_ Tsh (tarray tuint 16) v_v; data_at_ Tsh (tarray tuint 16) v_m;
        field_at sh t_blake2s_ctx (DOT _h) (map Vint (b2s_compress_n (Z.to_nat a) h t f0 inc bs)) ctx;
        field_at sh t_blake2s_ctx (DOT _t) [Vint (b2s_t0 (t + a * inc)); Vint (b2s_t1 (t + a * inc))] ctx;
        field_at sh t_blake2s_ctx (DOT _f) [Vint f0; Vint Int.zero] ctx;
        data_at dsh (tarray tuchar (64 * n)) (map Vubyte bs) data;
        blake2s_globals gv))%assert).
Proof.
intros SH H H2 H3 HRE H4.
remember (b2s_compress_n (Z.to_nat k) h t f0 inc bs) as hk eqn:Ehk.
remember (b2s_words (sublist (64 * k) (64 * k + 64) bs)) as mw eqn:Emw.
remember (b2s_v0 hk (b2s_t0 (t + k * inc + inc)) (b2s_t1 (t + k * inc + inc)) f0 Int.zero) as v0 eqn:Ev0.
assert (Hhk: Zlength hk = 8) by (rewrite Ehk; apply b2s_Zlength_compress_n; auto).
assert (Hmw: Zlength mw = 16) by (rewrite Emw; apply b2s_Zlength_words).
assert (Hv0: Zlength v0 = 16) by (subst v0; unfold b2s_v0; rewrite Zlength_app, Hhk; reflexivity).
assert (Hnext: b2s_feed hk (b2s_rounds mw v0 10) = b2s_compress_n (Z.to_nat (k + 1)) h t f0 inc bs)
  by (subst hk mw v0; apply b2s_compress_n_next; lia).
assert (Hvf: Zlength (b2s_rounds mw v0 10) = 16) by (rewrite b2s_Zlength_rounds; auto).
clear Ehk Emw Ev0.
eapply semax_seq'.
{ match goal with |- semax _ (PROPx _ (LOCALx _ (SEPx (_ :: _ :: _ :: ?a :: ?b :: ?c :: ?d :: nil)))) _ _ =>
    eapply semax_pre;
    [ | apply (b2s_rloop5_ok mw v0 v_v v_m ctx (offset_val (64 * k) data) (Vlong (Int64.repr (n - k)))
                (Vint (Int.repr inc)) gv (a * b * c * d)%logic Hmw Hv0) ] end.
  entailer!. }
Intros.
apply (b2s_feed5_ok sh ctx h t f0 dsh data n inc bs gv v_m v_v k hk (b2s_rounds mw v0 10) mw); auto.
Qed.
