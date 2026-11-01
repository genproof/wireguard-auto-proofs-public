(* The bodies of the protocol piece v5, group `small`: noise.c: the small functions, the identity and the handshake initialisation; port of prot4_noise_grp_noise_small.v, prot4_noise_grp_zero.v, prot4_noise_grp_noise_ident.v (wg_noise_set_static_identity_private_key: the v5 precondition, private key and flag uninitialised).
   Each function against its v5 specification (prot_specs5.v) in its unit's compspecs, with the context
   Gprot5 (prot_prog5.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.

(* the v4 helper lemmas (zeroed memory, the fields of the handshake and the identity, the big-endian
   stores), which mention neither the context nor a v5 predicate *)
Require Import WgNoise.proof.protocol4.prot4_noise_grp_noise_small.
Require Import WgNoise.proof.protocol4.prot4_noise_grp_zero.
Require Import WgNoise.proof.protocol4.prot4_noise_grp_noise_ident.
Require Import WgNoise.proof.protocol4.prot4_kp_bodies.

Section Small5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition G5s := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.

Lemma prot5_small_body_rounddown :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_quickproof_rounddown_pow_of_two quickproof_rounddown_pow_of_two_spec.
Proof.
  start_function. forward.
  forward_while (EX k: Z, PROP (0 <= k; 2 ^ k <= n)
    LOCAL (temp WgNoise.noise.code._r (Vlong (Int64.repr (2 ^ k)));
           temp WgNoise.noise.code._n (Vlong (Int64.repr n))) SEP ()).
  - Exists 0. entailer!.
  - entailer!.
  - forward.
    assert (0 <= n / 2 <= n)%Z by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rewrite Int64.unsigned_repr in HRE by rep_lia.
    assert (2 * 2 ^ k <= n)%Z by (pose proof (Z.mul_div_le n 2); lia).
    assert (E: (2 ^ (k + 1) = 2 ^ k * 2)%Z) by (rewrite Z.pow_add_r by lia; reflexivity).
    Exists (k + 1). entailer!. rewrite E. reflexivity.
  - forward.
    assert (0 <= n / 2 <= n)%Z by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
    rewrite Int64.unsigned_repr in HRE by rep_lia.
    assert (E: (2 ^ Z.succ k = 2 ^ k * 2)%Z) by (rewrite Z.pow_succ_r by lia; lia).
    assert (n < 2 ^ Z.succ k)%Z by (pose proof (Z.mod_pos_bound n 2); pose proof (Z.div_mod n 2); lia).
    rewrite (Z.log2_unique n k) by lia. entailer!.
Qed.

Lemma prot5_small_body_be32 :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_put_unaligned_be32 put_unaligned_be32_spec.
Proof.
  start_function. forward. forward. forward. forward. forward.
  unfold bytes_at. rewrite prot4_noise_small_be32_len, prot4_noise_small_be32_vals. entailer!.
Qed.

Section BE64.
(* the call put_unaligned_be32((u32)(v >> 32), p): VST's simpl must not unfold the shift *)
Local Opaque Int64.shru' Int64.shru.

Lemma prot5_small_body_be64 :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_put_unaligned_be64 put_unaligned_be64_spec.
Proof.
  start_function. assert_PROP (field_compatible (tarray tuchar 8) [] p) by entailer!.
  rewrite (split2_data_at__Tarray_tuchar sh 8 4) by (first [lia | exact H | destruct H; assumption]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact H | lia]).
  change (nested_field_offset (Tarray tuchar 8 noattr) (SUB 4)) with 4.
  replace (8 - 4) with 4 by lia. fold (tarray tuchar 4).
  forward_call (Int.repr (Int64.unsigned (Int64.shru' v (Int.repr 32))), sh, p).
  { cancel. }
  forward_call (Int.repr (Int64.unsigned v), sh, offset_val 4 p).
  rewrite prot4_noise_small_shru32.
  unfold bytes_at, be64, bytes. rewrite map_app, Zlength_app, !prot4_noise_small_be32_len.
  rewrite (split2_data_at_Tarray_app 4 8 sh tuchar)
    by (rewrite Zlength_map, prot4_noise_small_be32_len; reflexivity).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact H | lia]).
  change (nested_field_offset (Tarray tuchar 8 noattr) (SUB 4)) with 4.
  replace (8 - 4) with 4 by lia. entailer!.
Qed.
End BE64.

Lemma prot5_small_body_gensecret :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_curve25519_generate_secret curve25519_generate_secret_spec.
Proof.
  start_function. forward_call (gv, S, w, sh, p, 32). Intros r. unfold bytes_at. rewrite H.
  forward_call (sh, p, r). Exists r.
  assert (Zlength (clamp r) = 32) by (unfold clamp; list_solve).
  unfold bytes_at, bytes. rewrite H0. entailer!.
Qed.

Lemma prot5_small_body_hs_zero :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_handshake_zero handshake_zero_spec.
Proof.
  start_function. unfold hs_rep. Intros lk. unfold t_hs.
  assert_PROP (field_compatible (Tstruct I._noise_handshake noattr) (DOT I._ephemeral_private) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._remote_ephemeral) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._hash) h /\
    field_compatible (Tstruct I._noise_handshake noattr) (DOT I._chaining_key) h) as FC.
  { entailer!. }
  destruct FC as (FC1 & FC2 & FC3 & FC4).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._hash]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._hash] h, 0, 32).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._chaining_key]).
  forward_call (sh, field_address (Tstruct I._noise_handshake noattr) [StructField I._chaining_key] h, 0, 32).
  forward. forward.
  assert (Z0: bytes (zeros 32) = Zrepeat (Vubyte (Byte.repr 0)) 32) by reflexivity.
  unfold hs_rep, hs_zero.
  cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite Z0.
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._ephemeral_private]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._remote_ephemeral]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._hash]).
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._chaining_key]).
  Exists lk. entailer!.
  unfold hs_ok in *; simpl; tauto.
Qed.

Lemma prot5_small_body_tai64n :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_tai64n_now tai64n_now_spec.
Proof.
  start_function.
  forward_call (gv, S, w, Tsh, v_now).
  forward_call 20000000.
  change (2 ^ Z.log2 20000000) with 16777216.
  unfold t_timespec. forward. forward. forward.
  replace (Int64.not (Int64.sub (Int64.repr 16777216) (Int64.repr (Int.signed (Int.repr 1)))))
    with (Int64.not (Int64.repr 16777215)) by reflexivity.
  assert_PROP (field_compatible (tarray tuchar 12) [] p) as FC by entailer!.
  rewrite (split2_data_at__Tarray_tuchar sh 12 8) by (first [lia | exact FC | destruct FC; assumption]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  change (nested_field_offset (Tarray tuchar 12 noattr) (SUB 8)) with 8.
  replace (12 - 8) with 4 by lia. fold (tarray tuchar 4). fold (tarray tuchar 8).
  forward_call (Int64.add (Int64.repr 4611686018427387914) (s_rsec S), sh, p).
  { cancel. }
  forward.
  forward_call (Int.repr (Int64.unsigned (Int64.and (s_rnsec S) (Int64.not (Int64.repr 16777215)))),
                sh, offset_val 8 p).
  unfold tai64n, bytes_at, bytes. rewrite map_app, Zlength_app, !prot4_noise_small_be32_len.
  assert (L8: forall w, Zlength (be64 w) = 8) by reflexivity. rewrite L8.
  rewrite (split2_data_at_Tarray_app 8 12 sh tuchar)
    by (rewrite Zlength_map; first [apply L8 | apply prot4_noise_small_be32_len]).
  rewrite field_address0_offset by (apply arr_field_compatible0; [exact FC | lia]).
  change (nested_field_offset (Tarray tuchar 12 noattr) (SUB 8)) with 8.
  replace (12 - 8) with 4 by lia. entailer!.
Qed.

Lemma prot5_small_body_kp_create :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS WgNoise.noise.code.f_keypair_create (keypair_create_spec CSw).
Proof.
  start_function.
  forward_call (gv, S, w, 1200, Int.zero).
  Intros k.
  forward_if (k <> nullval).
  { destruct (eq_dec k nullval); [subst; entailer! | unfold bytes_at; entailer!]. }
  { subst k. forward. Exists nullval. rewrite !if_true by auto. entailer!. }
  { forward. entailer!. }
  Intros. rewrite !if_false by auto. Intros.
  rewrite prot4_zero_bytes_zeros_eq by lia.
  assert_PROP (malloc_compatible 1200 k) as MC.
  { sep_apply (@malloc_token_local_facts CSw Ews (tarray tuchar 1200) k). entailer!. }
  assert (FC: field_compatible t_kp [] k).
  { apply malloc_compatible_field_compatible; [exact MC | reflexivity | reflexivity]. }
  sep_apply (@prot4_zero_bytes_struct Noise.CS Noise.CS Ews t_kp k); auto.
  sep_apply (prot4_zero_kp_split Ews k).
  rewrite prot4_zero_ng_split. Intros. unfold t_atomic64, t_kp.
  forward. forward.
  forward. forward. forward. forward. forward. forward.
  Exists k. rewrite if_false by auto. rewrite prot4_zero_ng_split.
  unfold keypair_rep, entry_out, entry_at, entry_val, kp_fresh, symkey_val, prot4_zero_sym0.
  cbn [e_peer e_type e_index sk_key sk_birth sk_valid kp_send kp_scounter kp_recv kp_rcounter kp_backtrack
       kp_rindex kp_init kp_refs kp_id fst snd].
  rewrite <- prot4_zero_kp_entry_field by auto.
  Intros. Exists (Vint Int.zero) (Vint Int.zero).
  entailer!.
  { unfold kp_ok, zeros. cbn [sk_key kp_send kp_recv kp_backtrack]. rewrite !Zlength_Zrepeat by lia. auto. }
  unfold prot4_zero_kp_pad. apply derives_refl.
Qed.

Section FreeRcu.
(* kfree_sensitive's token is at CSw: keep forward_call from converting it *)
Local Ltac change_compspecs cs ::= idtac.

Lemma prot5_small_body_free_rcu :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_keypair_free_rcu (keypair_free_rcu_spec CSw).
Proof.
  start_function.
  assert_PROP (isptr k) by entailer!.
  assert (k <> nullval) by (destruct k; try contradiction; discriminate).
  forward_call (gv, S, w, k, SIZEOF_KEYPAIR).
  { entailer!. destruct k; try contradiction. simpl. rewrite prot4_kp_ofs by rep_lia. reflexivity. }
  { rewrite if_false by auto. cancel. }
  rewrite if_false by auto. entailer!.
Qed.
End FreeRcu.








Lemma prot5_small_body_precompute :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_wg_noise_precompute_static_static (wg_noise_precompute_static_static_spec x25519).
Proof.
  start_function.
  unfold hs_rep, identity_rep. Intros lkh lki.
  rewrite (prot4_noise_ident_sid_peer sh p (hs_sid H) H0).
  forward. forward.
  { entailer!. destruct (id_has ID); simpl; auto. }
  assert_PROP (field_compatible t_sid [] (hs_sid H)) as FCs by entailer!.
  assert (FCp: field_compatible t_sid (DOT I._static_private) (hs_sid H)) by auto with field_compatible.
  assert (FCss: field_compatible t_peer (DOT I._handshake DOT I._precomputed_static_static) p) by auto with field_compatible.
  assert (FCrs: field_compatible t_peer (DOT I._handshake DOT I._remote_static) p) by auto with field_compatible.
  rewrite prot4_noise_ident_sid_split, (prot4_noise_ident_ss_peer sh p _ H0), (prot4_noise_ident_rs_peer sh p _ H0).
  unfold wg_consts5. Intros.
  freeze [0;1;3;5;7;8;9;10;11;12;13;14;15;17;18;19;20;22] FR.
  forward_if (PROP () LOCAL (temp noise.code._t'1 (Val.of_bool (negb (id_has ID && dh_ok x25519 (id_priv ID) (hs_rstatic H)))); temp noise.code._peer p; gvars gv)
   SEP (FRZL FR;
   field_at sh t_peer (DOT I._handshake DOT I._static_identity) (hs_sid H) p;
   data_at sh (tarray tuchar 32) (bytes (hs_rstatic H)) (field_address t_peer (DOT I._handshake DOT I._remote_static) p);
   data_at sh (tarray tuchar 32) (bytes (if id_has ID then x25519 (id_priv ID) (hs_rstatic H) else hs_ss H)) (field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p);
   data_at shi (tarray tuchar 32) (bytes (id_priv ID)) (field_address t_sid (DOT I._static_private) (hs_sid H));
   curve25519_globals gv)).
  - forward. destruct (id_has ID); [inv H3|]. entailer!.
  - forward. destruct (id_has ID); [|inv H3].
    destruct H2 as [Hpub Hpriv]; destruct H1 as (?&Hrs&?).
    unfold bytes. forward_call (sh, field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p, shi, field_address t_sid (DOT I._static_private) (hs_sid H), id_priv ID, sh, field_address t_peer (DOT I._handshake DOT I._remote_static) p, hs_rstatic H, gv).
    forward. entailer!. unfold dh_ok. destruct (memneq_bool _ _); reflexivity.
  - destruct (andb (id_has ID) (dh_ok x25519 (id_priv ID) (hs_rstatic H))) eqn:Hb; simpl negb.
    + forward_if.
      { contradiction. }
      forward.
      pose proof Hb as Hb'. apply andb_prop in Hb' as [Hh _]. rewrite Hh.
      assert_PROP (Zlength (x25519 (id_priv ID) (hs_rstatic H)) = 32) as Lx.
      { entailer!. unfold bytes in *. rewrite Zlength_map in *. assumption. }
      unfold hs_rep, identity_rep, wg_consts5, precomputed. rewrite Hb. unfold hs_set_ss; cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
      thaw FR.
      rewrite <- (prot4_noise_ident_sid_peer sh p (hs_sid H) H0), <- (prot4_noise_ident_ss_peer sh p _ H0), <- (prot4_noise_ident_rs_peer sh p _ H0).
      entailer!.
      { destruct H1 as (?&?&?&?&?&?&?&?); repeat split; auto. }
      Exists lki. rewrite prot4_noise_ident_sid_split, exp_sepcon1. Exists lkh. cancel.
    + forward_if.
      2: { exfalso; apply Int.one_not_zero; assumption. }
      forward_call (sh, field_address t_peer (DOT I._handshake DOT I._precomputed_static_static) p, 0, 32).
      unfold hs_rep, identity_rep, wg_consts5, precomputed. rewrite Hb. unfold hs_set_ss; cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
      change (Zrepeat (Vubyte (Byte.repr 0)) 32) with (bytes zeros32).
      thaw FR.
      rewrite <- (prot4_noise_ident_sid_peer sh p (hs_sid H) H0), <- (prot4_noise_ident_ss_peer sh p _ H0), <- (prot4_noise_ident_rs_peer sh p _ H0).
      entailer!.
      { destruct H1 as (?&?&?&?&?&?&?&?); repeat split; auto. }
      Exists lki. rewrite prot4_noise_ident_sid_split, exp_sepcon1. Exists lkh. cancel.
Qed.

Lemma prot5_small_body_hs_init :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_init (wg_noise_handshake_init_spec x25519).
Proof.
  start_function.
  assert_PROP (field_compatible t_hs [] (hs_addr p)) as FCh by entailer!.
  sep_apply (@prot4_zero_data_at__bytes Noise.CS Noise.CS sh t_hs (hs_addr p)).
  change (@sizeof Noise.CS t_hs) with 304.
  forward_call (sh, hs_addr p, 0, 304).
  sep_apply (@prot4_zero_bytes_struct Noise.CS Noise.CS sh t_hs (hs_addr p)); auto.
  sep_apply (prot4_zero_hs_split sh (hs_addr p)).
  unfold hs_rep, entry_val, prot4_zero_HZ. Intros lk. unfold t_hs.
  cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex e_peer e_type e_index].
  forward. forward.
  unfold bytes_at. rewrite H0.
  rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._remote_static]).
  forward_call (sh, shk, field_address (Tstruct I._noise_handshake noattr) [StructField I._remote_static] (hs_addr p),
                pubp, 32, pub).
  forward_if (PROP () LOCAL (gvars gv; temp I._handshake (hs_addr p); temp I._static_identity sid;
      temp I._peer_public_key pubp; temp I._peer_preshared_key pskp; temp I._peer p)
    SEP (data_at sh (tarray tuchar 32) (map Vubyte pub)
           (field_address (Tstruct I._noise_handshake noattr) (DOT I._remote_static) (hs_addr p));
         data_at shk (tarray tuchar 32) (map Vubyte pub) pubp;
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._entry)
           (p, (nullval, (Val.of_bool false, (Vint (Int.repr 1), Vint Int.zero)))) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._state) (Vint Int.zero) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._last_initiation_consumption) (Vlong Int64.zero)
           (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._static_identity) nullval (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._ephemeral_private) (bytes zeros32) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._remote_ephemeral) (bytes zeros32) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._precomputed_static_static) (bytes zeros32)
           (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._preshared_key)
           (bytes (if eq_dec pskp nullval then zeros32 else psk)) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._hash) (bytes zeros32) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._chaining_key) (bytes zeros32) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._latest_timestamp) (bytes (zeros 12)) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._remote_index) (Vint Int.zero) (hs_addr p);
         field_at sh (Tstruct I._noise_handshake noattr) (DOT I._lock) lk (hs_addr p);
         spacer sh 36 40 (hs_addr p); spacer sh 300 304 (hs_addr p);
         identity_rep shi sid ID;
         if eq_dec pskp nullval then emp else data_at shq (tarray tuchar (Zlength psk)) (bytes psk) pskp;
         wg_consts5 gv)).
  { destruct (eq_dec pskp nullval) as [Hn|Hn]; [subst; entailer! | rewrite (H1 Hn); entailer!]. }
  { destruct (eq_dec pskp nullval) as [Hn|Hn]; [subst; contradiction|].
    rewrite (H1 Hn).
    rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._preshared_key]).
    forward_call (sh, shq, field_address (Tstruct I._noise_handshake noattr) [StructField I._preshared_key] (hs_addr p),
                  pskp, 32, psk).
    rewrite (field_at_data_at sh (Tstruct I._noise_handshake noattr) [StructField I._preshared_key]).
    rewrite (H1 Hn). simpl nested_field_type. entailer!. }
  { forward. destruct (eq_dec pskp nullval) as [Hn|Hn]; [|subst; contradiction]. entailer!. }
  forward. forward.
  set (psk' := if eq_dec pskp nullval then zeros32 else psk).
  set (H1' := mkHS HS_ZEROED Int64.zero sid zeros32 pub zeros32 zeros32 psk' zeros32 zeros32 (zeros 12) Int.zero).
  assert (Hok: hs_ok H1').
  { unfold hs_ok, H1', psk', zeros, zeros32. cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts].
    rewrite !Zlength_Zrepeat by lia. destruct (eq_dec pskp nullval); [rewrite Zlength_Zrepeat by lia|]; auto 10. }
  sep_apply (prot4_zero_hs_fold sh (hs_addr p) H1' lk Hok).
  forward_call (gv, sh, p, H1', shi, ID).
  { change (hs_sid H1') with sid. cancel. }
  change (hs_sid H1') with sid.
  replace (hs_set_ss H1' (precomputed x25519 ID (hs_rstatic H1'))) with (hs_initial x25519 ID sid pub psk')
    by reflexivity.
  unfold entry_out, entry_at, entry_val. cbn [e_peer e_type e_index].
  rewrite <- prot4_zero_entry_field by auto. unfold bytes_at. rewrite H0.
  entailer!.
  apply derives_refl.
Qed.

Lemma prot5_small_body_set_identity :
  @semax_body (QPvarspecs Noise.qp) G5s Noise.CS
    WgNoise.noise.code.f_wg_noise_set_static_identity_private_key (wg_noise_set_static_identity_private_key_spec x25519).
Proof.
  start_function.
  assert_PROP (field_compatible t_sid (DOT I._static_public) sid) as FC0 by entailer!.
  assert (FC: field_compatible t_sid [] sid) by (destruct FC0 as (?&?&?&?&?); repeat split; auto).
  unfold field_at_.
  rewrite (field_at_data_at sh t_sid [StructField I._static_private]).
  rewrite (field_at_data_at sh t_sid [StructField I._static_public]).
  simpl nested_field_type.
  unfold bytes_at, bytes; rewrite H.
  unfold wg_consts5; Intros.
  forward_call (sh, shk, field_address t_sid [StructField I._static_private] sid, pk, 32, raw).
  forward_call (sh, field_address t_sid [StructField I._static_private] sid, raw).
  forward_call (sh, field_address t_sid [StructField I._static_public] sid, map Vubyte pub, shk, pk, raw, gv).
  { entailer!. simpl. rewrite field_address_offset by auto with field_compatible. reflexivity. }
  { rewrite Zlength_map; auto. }
  forward.
  assert_PROP (Zlength (if memneq_bool raw zeros32 then map Vubyte (x25519 raw basepoint9) else map Vubyte pub) = 32) as L by entailer!.
  assert (Hcl: Zlength (clamp raw) = 32) by (unfold clamp; rewrite !upd_Znth_Zlength by list_solve; lia).
  assert (Hb: forall b, force_val (sem_cast_i2bool (Val.of_bool b)) = Val.of_bool b) by (destruct b; reflexivity).
  rewrite Hb.
  unfold identity_rep, identity_of, wg_consts5, bytes_at, bytes; simpl id_pub; simpl id_priv; simpl id_has.
  Exists (default_val (Tstruct noise.code._rw_semaphore noattr)).
  rewrite prot4_noise_ident_sid_split.
  destruct (memneq_bool raw zeros32); rewrite ?Zlength_map in L;
  (rewrite (field_at_data_at sh t_sid [StructField I._static_public]);
   simpl nested_field_type; rewrite ?H, ?Hcl, ?L; entailer!; split; auto).
Qed.


End Small5.

Theorem prot_bodies5_small :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_quickproof_rounddown_pow_of_two (quickproof_rounddown_pow_of_two_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_put_unaligned_be32 (put_unaligned_be32_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_put_unaligned_be64 (put_unaligned_be64_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_curve25519_generate_secret (curve25519_generate_secret_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_handshake_zero (handshake_zero_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_tai64n_now (tai64n_now_spec) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_keypair_create (keypair_create_spec CSw) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_keypair_free_rcu (keypair_free_rcu_spec CSw) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_set_static_identity_private_key (wg_noise_set_static_identity_private_key_spec x25519) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_precompute_static_static (wg_noise_precompute_static_static_spec x25519) /\
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_init (wg_noise_handshake_init_spec x25519).
Proof.
  intros. repeat match goal with |- _ /\ _ => split end;
  first [apply prot5_small_body_rounddown | apply prot5_small_body_be32 | apply prot5_small_body_be64
        | apply prot5_small_body_gensecret | apply prot5_small_body_hs_zero | apply prot5_small_body_tai64n
        | apply prot5_small_body_kp_create | apply prot5_small_body_free_rcu
        | apply prot5_small_body_set_identity | apply prot5_small_body_precompute
        | apply prot5_small_body_hs_init].
Qed.
