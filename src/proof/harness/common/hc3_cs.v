(* hc_pieces3: small compspecs for the common.h bodies.
   A common.h function has the same Clight in every law's unit, but the units' composite environments differ
   (clightgen drops unused structs).  Each body is proved ONCE at a small compspecs whose composites are in every
   unit that contains the function (cspecs_sub), then lifted (hc3_lift.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.harness.x_handshake.code WgNoise.harness.x_cookie_reply.code.
Require WgNoise.contracts.x_consume_initiation_any WgNoise.contracts.x_consume_response_any
        WgNoise.contracts.x_cookie_mac WgNoise.contracts.x_cookie_reply WgNoise.contracts.x_create_any
        WgNoise.contracts.x_handshake WgNoise.contracts.x_keypairs WgNoise.contracts.x_replay.

Module H := WgNoise.harness.x_handshake.code.
Module K := WgNoise.harness.x_cookie_reply.code.

Definition hc3_cname (c: composite_definition) : ident := match c with Composite i _ _ _ => i end.

Definition hc3_filter (names: list ident) (l: list composite_definition) : list composite_definition :=
  filter (fun c => existsb (Pos.eqb (hc3_cname c)) names) l.

(* the kernel structs (in every protocol law's unit) *)
Definition hc3_kernel_names : list ident :=
  [H.___gp_spinlock_t; H._rw_semaphore; H._rcu_head; H.___gp_atomic64_t; H._kref; H._blake2s_ctx;
   H._net_device; H._pubkey_hashtable; H._index_hashtable; H._index_hashtable_entry; H._noise_replay_counter;
   H._noise_symmetric_key; H._noise_keypair; H._noise_keypairs; H._noise_static_identity; H._noise_handshake;
   H._cookie_checker; H._cookie; H._wg_device; H._wg_peer].

(* kernel only: byte helpers, draws, m_hash2/hmac/kdf/dh/clamp/transport/label_key/mac, setup_*, table_*, ... *)
Definition hc3_comp_k : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ []) H.composites.
Definition hc3_prog_k := Clightdefs.mkprogram hc3_comp_k [] [] H._main Logic.I.
Definition CSk : compspecs := ltac:(make_compspecs hc3_prog_k).
(* + hs_snap: hs_take, hs_same, hs_zeroed_from *)
Definition hc3_comp_kh : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._hs_snap]) H.composites.
Definition hc3_prog_kh := Clightdefs.mkprogram hc3_comp_kh [] [] H._main Logic.I.
Definition CSkh : compspecs := ltac:(make_compspecs hc3_prog_kh).
(* + m_identity: m_identity_of, m_precomputed, m_static_public_field *)
Definition hc3_comp_ki : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._m_identity]) H.composites.
Definition hc3_prog_ki := Clightdefs.mkprogram hc3_comp_ki [] [] H._main Logic.I.
Definition CSki : compspecs := ltac:(make_compspecs hc3_prog_ki).
(* + m_identity, m_state: m_start, m_mix_*, m_encrypt_and_hash, m_decrypt_and_hash, m_consume_response *)
Definition hc3_comp_ks : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._m_identity; H._m_state]) H.composites.
Definition hc3_prog_ks := Clightdefs.mkprogram hc3_comp_ks [] [] H._main Logic.I.
Definition CSks : compspecs := ltac:(make_compspecs hc3_prog_ks).
(* + m_initiation: m_create_initiation *)
Definition hc3_comp_kinit : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._m_identity; H._m_state; H._m_initiation]) H.composites.
Definition hc3_prog_kinit := Clightdefs.mkprogram hc3_comp_kinit [] [] H._main Logic.I.
Definition CSkinit : compspecs := ltac:(make_compspecs hc3_prog_kinit).
(* + m_consumed_initiation: m_consume_initiation_1/2 *)
Definition hc3_comp_kci : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._m_identity; H._m_state; H._m_consumed_initiation]) H.composites.
Definition hc3_prog_kci := Clightdefs.mkprogram hc3_comp_kci [] [] H._main Logic.I.
Definition CSkci : compspecs := ltac:(make_compspecs hc3_prog_kci).
(* + m_response: m_create_response *)
Definition hc3_comp_kresp : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._m_identity; H._m_state; H._m_response]) H.composites.
Definition hc3_prog_kresp := Clightdefs.mkprogram hc3_comp_kresp [] [] H._main Logic.I.
Definition CSkresp : compspecs := ltac:(make_compspecs hc3_prog_kresp).
(* + the initiation message: init_img, fill_init *)
Definition hc3_comp_mi : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._message_header; H._message_macs; H._message_handshake_initiation]) H.composites.
Definition hc3_prog_mi := Clightdefs.mkprogram hc3_comp_mi [] [] H._main Logic.I.
Definition CSmi : compspecs := ltac:(make_compspecs hc3_prog_mi).
(* + the response message: resp_img, fill_resp *)
Definition hc3_comp_mr : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [H._message_header; H._message_macs; H._message_handshake_response]) H.composites.
Definition hc3_prog_mr := Clightdefs.mkprogram hc3_comp_mr [] [] H._main Logic.I.
Definition CSmr : compspecs := ltac:(make_compspecs hc3_prog_mr).
(* + ck_snap: ck_take, ck_same *)
Definition hc3_comp_kck : list composite_definition :=
  Eval vm_compute in hc3_filter (hc3_kernel_names ++ [K._ck_snap]) K.composites.
Definition hc3_prog_kck := Clightdefs.mkprogram hc3_comp_kck [] [] H._main Logic.I.
Definition CSkck : compspecs := ltac:(make_compspecs hc3_prog_kck).
