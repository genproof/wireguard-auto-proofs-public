(* the shim's refcount_t warnings wg_shim_refcount_warn[5] start at zero (an Init_space global);
   this introduces refwarn (prot_repr3.v, part of shim_state) from the initial global, for the harnesses' main. *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.

Lemma prot3_refwarn_intro (v: list val) (gv: globals) (i: ident) :
  i = _wg_shim_refcount_warn -> v = map Vlong (repeat Int64.zero 5) ->
  @data_at Noise.CS Ews (tarray tulong 5) v (gv i) |-- refwarn gv.
Proof. intros -> ->. unfold refwarn. Exists (repeat Int64.zero 5). entailer!. Qed.

(* the initial global as VST's process_globals gives it, in the world compspecs cs of a harness *)
Lemma prot3_refwarn_zero {cs: compspecs} {CCE: change_composite_env Noise.CS cs} (gv: globals) (i: ident) :
  i = _wg_shim_refcount_warn ->
  @data_at cs Ews (tarray tulong 5) (@zero_val cs (tarray tulong 5)) (gv i) |-- refwarn gv.
Proof.
  intros ->. unfold refwarn. Exists (repeat Int64.zero 5).
  rewrite prop_true_andp by reflexivity.
  assert (E: @data_at Noise.CS Ews (tarray tulong 5) (map Vlong (repeat Int64.zero 5)) =
             @data_at cs Ews (tarray tulong 5) (@zero_val cs (tarray tulong 5))).
  { apply data_at_change_composite; [| reflexivity].
    rewrite zero_val_eq. unfold tarray. rewrite (@zero_val_eq cs tulong). apply JMeq_refl. }
  rewrite <- E. apply derives_refl.
Qed.

(* the same after `autorewrite with zero_val` *)
Lemma prot3_refwarn_zrepeat {cs: compspecs} {CCE: change_composite_env Noise.CS cs} (gv: globals) (i: ident) :
  i = _wg_shim_refcount_warn ->
  @data_at cs Ews (tarray tulong 5) (Zrepeat (Vlong Int64.zero) 5) (gv i) |-- refwarn gv.
Proof.
  intros ->. unfold refwarn. Exists (repeat Int64.zero 5).
  rewrite prop_true_andp by reflexivity.
  assert (E: @data_at Noise.CS Ews (tarray tulong 5) (map Vlong (repeat Int64.zero 5)) =
             @data_at cs Ews (tarray tulong 5) (Zrepeat (Vlong Int64.zero) 5)).
  { apply data_at_change_composite; [apply JMeq_refl | reflexivity]. }
  rewrite <- E. apply derives_refl.
Qed.
