(* glue of the shared common.h layer (ht4c_spec.v) for the assemblies of the
   transport laws:
   - cs-independence of u32 arrays (minusp, the ChaCha state) and of ht4_minusp;
   - ht4c_<fn>_sub cs : funspec_sub (@ht4_<fn>_spec W_prim_aead) (@ht4_<fn>_spec cs) (byte / u32 arrays only:
     a main at its world W_<law> imports @ht4_<fn>_spec W_<law>, the bodies are at W_prim_aead);
   - the pieces of the shared bodies: u_ht4c (W_prim_aead, no varspecs, prim_aead's Clight: byte-identical in the
     transport harnesses), ht4c_piece1 (ht4c_G1), ht4c_piece_d (draw_size, draw_u64), and per law the piece of
     rp_final (its unit has the varspecs ht4c_Vmp mp and the law's Clight). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.subsume_funspec.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.assembly.asm_lib.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.harness.common4t.ht4c_spec.
Require WgNoise.proof.harness.common4t.ht4c_small_body WgNoise.proof.harness.common4t.ht4c_chacha_body
        WgNoise.proof.harness.common4t.ht4c_rp_body WgNoise.proof.harness.common4t.ht4c_rpmul_body
        WgNoise.proof.harness.common4t.ht4c_rpfinal_len WgNoise.proof.harness.common4t.ht4c_rpfinal_order
        WgNoise.proof.harness.common4t.ht4c_rpfinal_keepalive.
Require WgNoise.harness.x_prim_aead.code WgNoise.harness.x_transport_len.code WgNoise.harness.x_transport_order.code
        WgNoise.harness.x_transport_keepalive.code.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* u32 arrays are the same in every compspecs                              *)
(* ---------------------------------------------------------------------- *)

Lemma ht4c_align_tuint_cs (ce1 ce2: composite_env) n z :
  align_compatible_rec ce1 (tarray tuint n) z -> align_compatible_rec ce2 (tarray tuint n) z.
Proof.
  intros H. apply align_compatible_rec_Tarray. intros i Hi.
  eapply align_compatible_rec_Tarray_inv in H; [| exact Hi].
  inv H. econstructor; eauto.
Qed.

Lemma ht4c_field_compatible_tuint_cs {cs1 cs2: compspecs} n p :
  @field_compatible cs1 (tarray tuint n) [] p <-> @field_compatible cs2 (tarray tuint n) [] p.
Proof.
  unfold field_compatible, align_compatible, size_compatible; simpl.
  split; intros (? & ? & ? & ? & ?); repeat split; auto;
  destruct p; auto.
  all: first [ exact (ht4c_align_tuint_cs (@cenv_cs cs1) (@cenv_cs cs2) _ _ ltac:(eassumption))
             | exact (ht4c_align_tuint_cs (@cenv_cs cs2) (@cenv_cs cs1) _ _ ltac:(eassumption)) ].
Qed.

Lemma ht4c_data_at_tuint_cs {cs1 cs2: compspecs} sh n (v: list val) p :
  @data_at cs1 sh (tarray tuint n) v p = @data_at cs2 sh (tarray tuint n) v p.
Proof.
  unfold data_at, field_at. f_equal. f_equal. apply prop_ext. apply ht4c_field_compatible_tuint_cs.
Qed.

Lemma ht4c_data_at__tuint_cs {cs1 cs2: compspecs} sh n p :
  @data_at_ cs1 sh (tarray tuint n) p = @data_at_ cs2 sh (tarray tuint n) p.
Proof.
  unfold data_at_, field_at_, field_at. f_equal. f_equal. apply prop_ext. apply ht4c_field_compatible_tuint_cs.
Qed.

Lemma ht4_minusp_cs {cs1 cs2: compspecs} mp gv : @ht4_minusp cs1 mp gv = @ht4_minusp cs2 mp gv.
Proof. unfold ht4_minusp. apply ht4c_data_at_tuint_cs. Qed.

(* ---------------------------------------------------------------------- *)
(* the cs-change of the shared specifications                              *)
(* ---------------------------------------------------------------------- *)

Section Sub.
Context (cs: compspecs).

Ltac ht4c_rw :=
  repeat first [ rewrite (@aead_data_at_tuchar_cs W_prim_aead cs)
               | rewrite (@aead_data_at__tuchar_cs W_prim_aead cs)
               | rewrite (@ht4c_data_at_tuint_cs W_prim_aead cs)
               | rewrite (@ht4c_data_at__tuint_cs W_prim_aead cs)
               | rewrite (@ht4_minusp_cs W_prim_aead cs) ].

Ltac ht4c_sub :=
  apply NDsubsume_subsume; [split; reflexivity |];
  split; [split; reflexivity |];
  let x := fresh "x" in let g := fresh "gargs" in
  intros x g; Exists x (@emp mpred _ _); repeat (destruct x as [x ?]); simpl;
  rewrite emp_sepcon; ht4c_rw;
  apply andp_right; [apply andp_left2; auto |];
  apply prop_right; let r := fresh "rho" in intros r; rewrite emp_sepcon; apply andp_left2; ht4c_rw;
  first [apply derives_refl | auto].

(* check_failed, draw_size, draw_u64, rc_rotl: no memory, their specifications do not depend on the compspecs *)
Lemma ht4c_bytes_eq_sub :
  funspec_sub (snd (@ht4_bytes_eq_spec W_prim_aead)) (snd (@ht4_bytes_eq_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_bytes_copy_sub :
  funspec_sub (snd (@ht4_bytes_copy_spec W_prim_aead)) (snd (@ht4_bytes_copy_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_bytes_set_sub :
  funspec_sub (snd (@ht4_bytes_set_spec W_prim_aead)) (snd (@ht4_bytes_set_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_le32_store_sub :
  funspec_sub (snd (@ht4_le32_store_spec W_prim_aead)) (snd (@ht4_le32_store_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_le32_load_sub :
  funspec_sub (snd (@ht4_le32_load_spec W_prim_aead)) (snd (@ht4_le32_load_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_le64_store_sub :
  funspec_sub (snd (@ht4_le64_store_spec W_prim_aead)) (snd (@ht4_le64_store_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_le64_load_sub :
  funspec_sub (snd (@ht4_le64_load_spec W_prim_aead)) (snd (@ht4_le64_load_spec cs)).
Proof. ht4c_sub. Qed.
Lemma ht4c_rc_qr_sub :
  funspec_sub (snd (@ht4_rc_qr_spec W_prim_aead)) (snd (@ht4_rc_qr_spec cs)).
Proof. ht4c_sub. Qed.
(* rc_rounds, rc_setup, ref_chacha20_block: not imported by a main (their posts unfold badly under simpl) *)

End Sub.

(* ---------------------------------------------------------------------- *)
(* the pieces of the shared bodies                                         *)
(* ---------------------------------------------------------------------- *)

(* the unit of the shared bodies: prim_aead's Clight (byte-identical in the transport harnesses), W_prim_aead,
   no varspecs *)
Definition u_ht4c : unit_ctx := mk_unit W_prim_aead [] WgNoise.harness.x_prim_aead.code.prog.

Module PC := WgNoise.harness.x_prim_aead.code.

Ltac ht4c_ver f B :=
  exists u_ht4c; split; [left; reflexivity |]; exists f; split; [reflexivity | exact B].

Theorem ht4c_piece1 : piece_ok [u_ht4c] (fun _ => []) ht4c_G1.
Proof.
  destruct WgNoise.proof.harness.common4t.ht4c_small_body.ht4c_small_bodies
    as (S1 & S2 & S3 & S4 & _ & _ & S7 & S8 & S9 & _).
  destruct WgNoise.proof.harness.common4t.ht4c_chacha_body.ht4c_chacha_bodies as (C1 & C2 & C3 & C4 & C5).
  destruct WgNoise.proof.harness.common4t.ht4c_rp_body.ht4c_rp_bodies as (R1 & R2 & R3).
  pose proof WgNoise.proof.harness.common4t.ht4c_rpmul_body.ht4cm_rpmul_body as R4.
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  change ((fun _ : compspecs => @nil (ident * funspec)) (u_cs u_ht4c) ++ ht4c_G1) with ht4c_G1.
  repeat constructor.
  - ht4c_ver PC.f_check_failed S1.
  - ht4c_ver PC.f_bytes_eq S2.
  - ht4c_ver PC.f_bytes_copy S3.
  - ht4c_ver PC.f_bytes_set S4.
  - ht4c_ver PC.f_le32_store S7.
  - ht4c_ver PC.f_le32_load S8.
  - ht4c_ver PC.f_le64_store S9.
  - ht4c_ver PC.f_rc_rotl C1.
  - ht4c_ver PC.f_rc_qr C2.
  - ht4c_ver PC.f_rc_rounds C3.
  - ht4c_ver PC.f_rc_setup C4.
  - ht4c_ver PC.f_ref_chacha20_block C5.
  - ht4c_ver PC.f_rp_add R1.
  - ht4c_ver PC.f_rp_init R2.
  - ht4c_ver PC.f_rp_mul R4.
  - ht4c_ver PC.f_rp_block R3.
Qed.

(* draw_size / draw_u64 (transport_len, transport_order): proved with ht4c_Gd, lifted to ht4c_Gd ++ ht4c_Gdraw *)
Definition ht4c_Gdraw : funspecs := [ht4_draw_size_spec; ht4_draw_u64_spec].

Lemma ht4c_draw_lift f ip :
  @semax_body [] ht4c_Gd W_prim_aead f ip -> @semax_body [] (ht4c_Gd ++ ht4c_Gdraw) W_prim_aead f ip.
Proof.
  intros SB. apply (@semax_body_subsumption W_prim_aead [] [] ht4c_Gd _ f ip SB).
  apply tycontext_sub_i99. split; intro i.
  - rewrite !asm_make_tycontext_g. unfold ht4c_Gd, ht4c_Gdraw; simpl.
    repeat (if_tac; [reflexivity |]). simpl; auto.
  - rewrite !semax_prog.find_id_maketycontext_s. unfold ht4c_Gd, ht4c_Gdraw; simpl.
    repeat (if_tac; [eexists; split; [reflexivity | apply seplog.funspec_sub_si_refl] |]). simpl. auto.
Qed.

Theorem ht4c_piece_d : piece_ok [u_ht4c] (fun _ => ht4c_Gd) ht4c_Gdraw.
Proof.
  destruct WgNoise.proof.harness.common4t.ht4c_small_body.ht4c_small_bodies
    as (_ & _ & _ & _ & S5 & S6 & _).
  split; [vm_compute; repeat constructor; simpl; intuition discriminate |].
  repeat constructor.
  - exists u_ht4c; split; [left; reflexivity |]; exists PC.f_draw_size; split; [reflexivity |].
    apply ht4c_draw_lift, S5.
  - exists u_ht4c; split; [left; reflexivity |]; exists PC.f_draw_u64; split; [reflexivity |].
    apply ht4c_draw_lift, S6.
Qed.

(* rp_final, per law: the law's Clight (its minusp), the varspecs [(mp, u32[17])] *)
Definition u_ht4c_rpf (mp: ident) (prog: Clight.program) : unit_ctx := mk_unit W_prim_aead (ht4c_Vmp mp) prog.

Theorem ht4c_piece_rpf_len :
  piece_ok [u_ht4c_rpf WgNoise.harness.x_transport_len.code._x_transport_len__minusp WgNoise.harness.x_transport_len.code.prog]
    (fun _ => ht4c_G1) [rp_final_spec_of WgNoise.harness.x_transport_len.code._x_transport_len__minusp].
Proof.
  split; [repeat constructor; simpl; intuition |].
  repeat constructor. eexists; split; [left; reflexivity |].
  exists WgNoise.harness.x_transport_len.code.f_rp_final; split; [reflexivity |].
  exact WgNoise.proof.harness.common4t.ht4c_rpfinal_len.ht4cl_rp_final_body.
Qed.

Theorem ht4c_piece_rpf_order :
  piece_ok [u_ht4c_rpf WgNoise.harness.x_transport_order.code._x_transport_order__minusp WgNoise.harness.x_transport_order.code.prog]
    (fun _ => ht4c_G1) [rp_final_spec_of WgNoise.harness.x_transport_order.code._x_transport_order__minusp].
Proof.
  split; [repeat constructor; simpl; intuition |].
  repeat constructor. eexists; split; [left; reflexivity |].
  exists WgNoise.harness.x_transport_order.code.f_rp_final; split; [reflexivity |].
  exact WgNoise.proof.harness.common4t.ht4c_rpfinal_order.ht4co_rp_final_body.
Qed.

Theorem ht4c_piece_rpf_keepalive :
  piece_ok [u_ht4c_rpf WgNoise.harness.x_transport_keepalive.code._x_transport_keepalive__minusp WgNoise.harness.x_transport_keepalive.code.prog]
    (fun _ => ht4c_G1) [rp_final_spec_of WgNoise.harness.x_transport_keepalive.code._x_transport_keepalive__minusp].
Proof.
  split; [repeat constructor; simpl; intuition |].
  repeat constructor. eexists; split; [left; reflexivity |].
  exists WgNoise.harness.x_transport_keepalive.code.f_rp_final; split; [reflexivity |].
  exact WgNoise.proof.harness.common4t.ht4c_rpfinal_keepalive.ht4ck_rp_final_body.
Qed.
