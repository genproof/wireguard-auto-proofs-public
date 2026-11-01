(* The ChaCha20 inlines of include/crypto/chacha.h that harness/ae_split_chacha20.c compiles into its own unit
   (chacha_init_consts, chacha_init, chacha20_crypt), proved on the harness's copies in the law's world
   W_ae_split_chacha20, each with a context of its callees only, against their shared specifications
   (aead_spec.v, aead_spec3.v; stated at Chacha20poly1305.CS, whose copies aead_small_body3.v and
   aead_chacha_body3.v prove with the same steps).  The structs are converted between Chacha20poly1305.CS /
   Chacha.CS and the world with change_composite_env (struct chacha_state is the same in all three). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.aead.aead_chacha_body3.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_world.
Require Import WgNoise.proof.harness.ae_split_chacha20.ae_split_chacha20_spec.
Require WgNoise.harness.ae_split_chacha20.code.

Local Open Scope Z_scope.

#[local] Existing Instance W_ae_split_chacha20.

#[export] Instance asc_cce_c20p_W : change_composite_env Chacha20poly1305.CS W_ae_split_chacha20.
Proof. make_cs_preserve Chacha20poly1305.CS W_ae_split_chacha20. Defined.
#[export] Instance asc_cce_W_c20p : change_composite_env W_ae_split_chacha20 Chacha20poly1305.CS.
Proof. make_cs_preserve W_ae_split_chacha20 Chacha20poly1305.CS. Defined.
#[export] Instance asc_cce_chacha_W : change_composite_env Chacha.CS W_ae_split_chacha20.
Proof. make_cs_preserve Chacha.CS W_ae_split_chacha20. Defined.
#[export] Instance asc_cce_W_chacha : change_composite_env W_ae_split_chacha20 Chacha.CS.
Proof. make_cs_preserve W_ae_split_chacha20 Chacha.CS. Defined.

(* struct chacha_state: the same data_at in Chacha20poly1305.CS and in the world *)
Lemma asc_state_cs sh (v: list val) p :
  @data_at Chacha20poly1305.CS sh t_chacha_state v p = @data_at W_ae_split_chacha20 sh t_chacha_state v p.
Proof.
  exact (f_equal (fun f => f p) (@data_at_change_composite Chacha20poly1305.CS W_ae_split_chacha20 asc_cce_c20p_W sh
    t_chacha_state v v (JMeq_refl _) eq_refl)).
Qed.

Lemma asc_state__cs sh p :
  @data_at_ Chacha20poly1305.CS sh t_chacha_state p = @data_at_ W_ae_split_chacha20 sh t_chacha_state p.
Proof. rewrite !data_at__eq. apply asc_state_cs. Qed.

Lemma body_chacha_init_consts_asc :
  semax_body asc_V nil WgNoise.harness.ae_split_chacha20.code.f_chacha_init_consts chacha_init_consts_spec.
Proof.
  start_function.
  rewrite asc_state_cs.
  forward. forward. forward. forward.
  rewrite asc_state_cs.
  entailer!. apply derives_refl'. f_equal. unfold chacha_consts. list_solve.
Qed.

Lemma body_chacha_init_asc :
  semax_body asc_V [chacha_init_consts_spec; get_unaligned_le32_spec]
    WgNoise.harness.ae_split_chacha20.code.f_chacha_init chacha_init_spec.
Proof.
  start_function.
  rewrite asc_state__cs, data_at__eq. change (default_val t_chacha_state) with (Zrepeat Vundef 16).
  forward_call (sh, state, Zrepeat Vundef 16).
  rewrite asc_state_cs.
  change_compspecs W_ae_split_chacha20.
  forward. forward. forward. forward. forward. forward. forward. forward.
  forward. forward. forward. forward. forward. forward. forward. forward.
  assert_PROP (isptr ivp) as Piv by entailer!. destruct ivp; try contradiction.
  forward_call (ish, Vptr b i, 0, iv).
  forward.
  forward_call (ish, Vptr b i, 4, iv).
  forward.
  forward_call (ish, Vptr b i, 8, iv).
  forward.
  forward_call (ish, Vptr b i, 12, iv).
  forward.
  rewrite asc_state_cs.
  entailer!. apply derives_refl'. f_equal. unfold chacha_init_st, chacha_consts. list_solve.
Qed.

Lemma body_chacha20_crypt_asc :
  semax_body asc_V [chacha_crypt_spec3]
    WgNoise.harness.ae_split_chacha20.code.f_chacha20_crypt chacha20_crypt_spec3.
Proof.
  start_function.
  rewrite asc_state_cs.
  rewrite (@cb3_prim_bytes_cs Chacha20poly1305.CS Chacha.CS).
  rewrite (@cb3_prim_out_cs Chacha20poly1305.CS Chacha.CS).
  forward_call (ssh, state, st, dsh, dst, msh, src, m, 20).
  rewrite (@cb3_prim_bytes_cs Chacha.CS Chacha20poly1305.CS).
  rewrite (@cb3_prim_out_cs Chacha.CS Chacha20poly1305.CS).
  change (Z.to_nat (20 / 2)) with 10%nat.
  rewrite asc_state_cs.
  entailer!.
Qed.
