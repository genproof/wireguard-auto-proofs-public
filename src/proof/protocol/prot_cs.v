(* Converting the protocol's object predicates between compspecs.

   The representation (prot_repr.v) is stated in Noise.CS (sk_buff and the cookie message: Cookie.CS).  A body
   proof in the shim or cookie unit converts the predicates it touches to its own compspecs before loading /
   storing, and back before the postcondition, with data_at_cs_eq / field_at_cs_eq below (the instances make
   them one-liners; building one instance takes ~1.5 s, done once here).  Example (tested):

     Lemma N2S_tulong sh v p : @data_at Noise.CS sh tulong v p = @data_at Shim.CS sh tulong v p.
     Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.
     ... unfold shim_state; Intros; rewrite !N2S_tulong; forward ...
   (change_compspecs does not handle scalar data_at.) *)
Require Import VST.floyd.proofauto.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.

#[export] Instance CCE_Noise_Shim : change_composite_env Noise.CS Shim.CS.
Proof. make_cs_preserve Noise.CS Shim.CS. Defined.
#[export] Instance CCE_Shim_Noise : change_composite_env Shim.CS Noise.CS.
Proof. make_cs_preserve Shim.CS Noise.CS. Defined.
#[export] Instance CCE_Noise_Cookie : change_composite_env Noise.CS Cookie.CS.
Proof. make_cs_preserve Noise.CS Cookie.CS. Defined.
#[export] Instance CCE_Cookie_Noise : change_composite_env Cookie.CS Noise.CS.
Proof. make_cs_preserve Cookie.CS Noise.CS. Defined.
#[export] Instance CCE_Cookie_Shim : change_composite_env Cookie.CS Shim.CS.
Proof. make_cs_preserve Cookie.CS Shim.CS. Defined.
#[export] Instance CCE_Shim_Cookie : change_composite_env Shim.CS Cookie.CS.
Proof. make_cs_preserve Shim.CS Cookie.CS. Defined.

(* data_at / field_at of a type whose composites agree: the same predicate *)
Lemma data_at_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

Lemma field_at_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (gfs: list gfield)
  (v1: @reptype cs1 (@nested_field_type cs1 t gfs)) (v2: @reptype cs2 (@nested_field_type cs2 t gfs)) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @field_at cs1 sh t gfs v1 p = @field_at cs2 sh t gfs v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@field_at_change_composite cs1 cs2 CCE sh t gfs v1 v2 H H0)). Qed.

Lemma data_at__cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (p: val) :
  cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at_ cs1 sh t p = @data_at_ cs2 sh t p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at__change_composite cs1 cs2 CCE sh t H)). Qed.

Lemma N2S_tulong sh v p : @data_at Noise.CS sh tulong v p = @data_at Shim.CS sh tulong v p.
Proof. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.
