(* part of x25519_part3: the body of fe_mul_121666_impl.
   Specifications: x25519_spec.v, model: x25519_model.v. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.x25519.x25519_spec.

#[local] Existing Instance Curve25519Fiat32.CS.

Ltac abbrev_head3 :=
  match goal with
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vlong ?e) :: _) _)) _ _ =>
      tryif is_var e then idtac else (let x := fresh "l" in remember e as x)
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vint (Int.repr _)) :: _) _)) _ _ => idtac
  | |- semax _ (PROPx _ (LOCALx (temp _ (Vint ?e) :: _) _)) _ _ =>
      tryif is_var e then idtac else (let x := fresh "i" in remember e as x)
  | |- _ => idtac
  end.

Ltac fw3 := forward; abbrev_head3.

Theorem x25519_mul121666_3 : semax_body x25_V x25_Gprog F.f_fe_mul_121666_impl fe_mul_121666_impl_spec.
Proof.
  start_function.
  do 10 forward.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  do 10 fw3.
  fw3.
  do 5 forward.
  do 5 forward.
  assert (Hm: fe_mul121666_m f = [i9; i12; Int.add i11 i1; i2; i3; i4; i5; i6; i7; i8]).
  { subst. unfold fe_mul121666_m, u64, lo. cbv zeta. f_equal. }
  rewrite Hm. clear Hm. go_lower.
  match goal with |- data_at _ _ ?a _ * _ |-- data_at _ _ ?b _ * _ =>
    replace a with b by reflexivity end.
  apply derives_refl.
Qed.
