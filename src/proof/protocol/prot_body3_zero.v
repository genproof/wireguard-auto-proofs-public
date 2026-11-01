(* Body proofs of the protocol piece, group zero.
   Target: prot_bodies3_zero.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

(* ------------------------------------------------------------------------------------------------ *)
(* Zeroed memory as data_at of zero values                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Lemma prot3_zero_mapsto_byte_zero {cs: compspecs} sh b ofs :
  readable_share sh -> 0 <= ofs -> ofs + 1 < Ptrofs.modulus ->
  mapsto sh tuchar (Vptr b (Ptrofs.repr ofs)) (Vint Int.zero) |-- mapsto_zeros 1 sh (Vptr b (Ptrofs.repr ofs)).
Proof.
  intros. unfold mapsto, mapsto_zeros. simpl. rewrite if_true by auto.
  rewrite Ptrofs.unsigned_repr by rep_lia.
  apply orp_left; [ | apply derives_extract_prop; intro Hx; discriminate Hx].
  apply andp_left2. apply andp_right; [apply prop_right; lia | ].
  change (predicates_sl.sepcon ?a ?b) with (sepcon a b). change predicates_sl.emp with emp.
  rewrite sepcon_emp. apply derives_refl.
Qed.

Lemma prot3_zero_bytes_zeros_nat {cs: compspecs} sh b (n: nat) : forall ofs,
  readable_share sh -> 0 <= ofs -> ofs + Z.of_nat n < Ptrofs.modulus ->
  data_at sh (tarray tuchar (Z.of_nat n)) (Zrepeat (Vubyte Byte.zero) (Z.of_nat n)) (Vptr b (Ptrofs.repr ofs))
  |-- mapsto_zeros (Z.of_nat n) sh (Vptr b (Ptrofs.repr ofs)).
Proof.
induction n; intros ofs Hsh H0 H1.
- simpl. change predicates_sl.emp with emp. rewrite Ptrofs.unsigned_repr by rep_lia. entailer!.
  apply data_at_zero_array_inv; auto.
- rewrite Nat2Z.inj_succ in *. unfold tarray.
  assert_PROP (field_compatible (Tarray tuchar (Z.succ (Z.of_nat n)) noattr) [] (Vptr b (Ptrofs.repr ofs)))
    as FC by entailer!.
  rewrite (split2_data_at_Tarray_tuchar sh (Z.succ (Z.of_nat n)) 1) by (try rewrite Zlength_Zrepeat; lia).
  assert (FC0: field_compatible0 (Tarray tuchar (Z.succ (Z.of_nat n)) noattr) [ArraySubsc 1]
                 (Vptr b (Ptrofs.repr ofs)))
    by (apply field_compatible0_cons; simpl; split; [lia | auto with field_compatible]).
  rewrite field_address0_offset by auto.
  replace (Z.succ (Z.of_nat n)) with (1 + Z.of_nat n) by lia.
  rewrite (aggregate_pred.mapsto_zeros_split sh b ofs 1 (Z.of_nat n)) by lia.
  rewrite sublist_Zrepeat, sublist_Zrepeat by lia.
  replace (1 + Z.of_nat n - 1) with (Z.of_nat n) by lia.
  apply sepcon_derives.
  + rewrite (data_at_singleton_array_eq sh tuchar (Vubyte Byte.zero)) by reflexivity.
    assert_PROP (field_compatible tuchar [] (Vptr b (Ptrofs.repr ofs))) by entailer!.
    rewrite <- (mapsto_data_at' sh tuchar (Vubyte Byte.zero) (Vubyte Byte.zero)) by (auto; reflexivity).
    apply prot3_zero_mapsto_byte_zero; auto; lia.
  + replace (offset_val _ _) with (Vptr b (Ptrofs.repr (ofs + 1))).
    * apply IHn; auto; lia.
    * simpl. f_equal. rewrite Ptrofs.add_unsigned, !Ptrofs.unsigned_repr by rep_lia. reflexivity.
Qed.

Lemma prot3_zero_bytes_zeros {cs: compspecs} sh n p :
  readable_share sh -> 0 <= n ->
  data_at sh (tarray tuchar n) (Zrepeat (Vubyte Byte.zero) n) p |-- mapsto_zeros n sh p.
Proof.
  intros Hsh Hn.
  assert_PROP (field_compatible (tarray tuchar n) [] p) as FC by entailer!.
  destruct p; try (destruct FC; contradiction).
  destruct FC as [_ [_ [SC _]]]. simpl in SC. rewrite Z.max_r in SC by lia.
  rewrite <- (Ptrofs.repr_unsigned i). rewrite <- (Z2Nat.id n) by lia.
  apply prot3_zero_bytes_zeros_nat; auto; rewrite ?Z2Nat.id by lia; rep_lia.
Qed.

(* a struct's undefined memory as a byte array (for memset) *)
Lemma prot3_zero_data_at__bytes {cs1 cs2: compspecs} sh t p :
  @data_at_ cs1 sh t p |-- @data_at_ cs2 sh (tarray tuchar (@sizeof cs1 t)) p.
Proof.
  rewrite data_at__memory_block. apply derives_extract_prop; intro FC.
  apply memory_block_data_at__tarray_tuchar.
  destruct FC as (PT & _ & SC & _). destruct p as [| | | | | b i]; try contradiction. simpl in SC.
  pose proof (@sizeof_pos cs1 t). pose proof (Ptrofs.unsigned_range i). lia.
Qed.

(* memset's zero bytes as the struct of zero values *)
Lemma prot3_zero_bytes_struct {cs1 cs2: compspecs} sh t p :
  readable_share sh ->
  @complete_legal_cosu_type (@cenv_cs cs1) t = true ->
  @fully_nonvolatile cs1 (rank_type (@cenv_cs cs1) t) t = true ->
  @field_compatible cs1 t [] p ->
  @data_at cs2 sh (tarray tuchar (@sizeof cs1 t)) (Zrepeat (Vubyte Byte.zero) (@sizeof cs1 t)) p
  |-- @data_at cs1 sh t (zero_val t) p.
Proof.
  intros Hsh L NV FC.
  sep_apply (@prot3_zero_bytes_zeros cs2 sh (@sizeof cs1 t) p Hsh). { pose proof (@sizeof_pos cs1 t); lia. }
  apply mapsto_zero_data_at_zero; auto.
Qed.

(* ------------------------------------------------------------------------------------------------ *)
(* wg_noise_handshake_init                                                                          *)
(* ------------------------------------------------------------------------------------------------ *)

Local Open Scope logic.

Definition prot3_zero_HZ : handshake :=
  mkHS Int.zero Int64.zero nullval zeros32 zeros32 zeros32 zeros32 zeros32 zeros32 zeros32 (zeros 12) Int.zero.

(* the top-level padding of struct noise_handshake *)
Definition prot3_zero_hs_pad (sh: share) (h: val) : mpred :=
  spacer sh 36 40 h * spacer sh 300 304 h.

Definition prot3_zero_hs_zero_val : @reptype Noise.CS t_hs :=
  ((nullval, (nullval, (Vint Int.zero, (Vint Int.zero, Vint Int.zero)))),
   (Vint Int.zero, (Vlong Int64.zero, (nullval, (bytes zeros32, (bytes zeros32, (bytes zeros32,
   (bytes zeros32, (bytes zeros32, (bytes zeros32, (bytes zeros32, (bytes (zeros 12),
   (Vint Int.zero, Vint Int.zero))))))))))))).

Lemma prot3_zero_hs_zero_val_eq : @zero_val Noise.CS t_hs = prot3_zero_hs_zero_val.
Proof.
  apply JMeq_eq. eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]. apply JMeq_refl.
Qed.

Section HSZero.
#[local] Existing Instance Noise.CS.

Lemma prot3_zero_hs_split sh h :
  @data_at Noise.CS sh t_hs (zero_val t_hs) h |--
  @field_at Noise.CS sh t_hs (DOT I._entry) (entry_val (mkEntry nullval Int.zero Int.zero) nullval false) h *
  hs_rep sh h prot3_zero_HZ.
Proof.
  rewrite prot3_zero_hs_zero_val_eq. unfold prot3_zero_hs_zero_val.
  unfold_data_at (data_at _ _ _ _).
  unfold hs_rep, prot3_zero_HZ, spacer, at_offset.
  cbn [hs_state hs_lic hs_sid hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex].
  rewrite prop_true_andp by (unfold hs_ok, zeros; cbn [hs_eph hs_rstatic hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts];
    rewrite !Zlength_Zrepeat by lia; auto 10).
  Exists (Vint Int.zero).
  repeat match goal with |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b); [lia|] end.
  change (40 - 36) with 4. change (304 - 300) with 4.
  cancel.
Qed.

Lemma prot3_zero_hs_fold sh h H lk :
  hs_ok H ->
  field_at sh t_hs (DOT I._state) (Vint (hs_state H)) h *
  field_at sh t_hs (DOT I._last_initiation_consumption) (Vlong (hs_lic H)) h *
  field_at sh t_hs (DOT I._static_identity) (hs_sid H) h *
  field_at sh t_hs (DOT I._ephemeral_private) (bytes (hs_eph H)) h *
  data_at sh (tarray tuchar 32) (bytes (hs_rstatic H)) (field_address t_hs (DOT I._remote_static) h) *
  field_at sh t_hs (DOT I._remote_ephemeral) (bytes (hs_reph H)) h *
  field_at sh t_hs (DOT I._precomputed_static_static) (bytes (hs_ss H)) h *
  field_at sh t_hs (DOT I._preshared_key) (bytes (hs_psk H)) h *
  field_at sh t_hs (DOT I._hash) (bytes (hs_hash H)) h *
  field_at sh t_hs (DOT I._chaining_key) (bytes (hs_ck H)) h *
  field_at sh t_hs (DOT I._latest_timestamp) (bytes (hs_ts H)) h *
  field_at sh t_hs (DOT I._remote_index) (Vint (hs_rindex H)) h *
  field_at sh t_hs (DOT I._lock) lk h *
  spacer sh 36 40 h * spacer sh 300 304 h
  |-- hs_rep sh h H.
Proof.
  intros Hok. unfold hs_rep. rewrite prop_true_andp by auto. Exists lk.
  rewrite (field_at_data_at sh t_hs (DOT I._remote_static)). simpl nested_field_type. cancel.
Qed.

Lemma prot3_zero_entry_field sh h v :
  field_compatible t_hs [] h ->
  field_at sh t_hs (DOT I._entry) v h = data_at sh t_entry_s v h.
Proof.
  intros FC. rewrite field_at_data_at. unfold field_address. rewrite if_true by auto with field_compatible.
  simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible. reflexivity.
Qed.

(* keypairs *)
Definition prot3_zero_kp_zero_val : @reptype Noise.CS t_kp :=
  ((nullval, (nullval, (Vint Int.zero, (Vint Int.zero, Vint Int.zero)))),
   ((bytes zeros32, (Vlong Int64.zero, Vint Int.zero)),
    (Vlong Int64.zero,
     ((bytes zeros32, (Vlong Int64.zero, Vint Int.zero)),
      ((Vlong Int64.zero, (Vint Int.zero, map Vlong (Zrepeat Int64.zero 128))),
       (Vint Int.zero, (Vint Int.zero, (Vint Int.zero, (Vint Int.zero, Vlong Int64.zero))))))))).

Lemma prot3_zero_kp_zero_val_eq : @zero_val Noise.CS t_kp = prot3_zero_kp_zero_val.
Proof.
  apply JMeq_eq. eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |]. apply JMeq_refl.
Qed.

(* the top-level padding of struct noise_keypair *)
Definition prot3_zero_kp_pad (sh: share) (k: val) : mpred := spacer sh 1181 1184 k.

Definition prot3_zero_sym0 : symkey := mkSym zeros32 Int64.zero false.

Lemma prot3_zero_kp_split sh k :
  @data_at Noise.CS sh t_kp (zero_val t_kp) k |--
  field_at sh t_kp (DOT I._entry) (entry_val (mkEntry nullval Int.zero Int.zero) nullval false) k *
  field_at sh t_kp (DOT I._sending) (symkey_val prot3_zero_sym0) k *
  field_at sh t_kp (DOT I._sending_counter) (Vlong Int64.zero) k *
  field_at sh t_kp (DOT I._receiving) (symkey_val prot3_zero_sym0) k *
  field_at sh t_kp (DOT I._receiving_counter)
    (Vlong Int64.zero, (Vint Int.zero, map Vlong (Zrepeat Int64.zero 128))) k *
  field_at sh t_kp (DOT I._remote_index) (Vint Int.zero) k *
  field_at sh t_kp (DOT I._i_am_the_initiator) (Val.of_bool false) k *
  field_at sh t_kp (DOT I._refcount) (Vint Int.zero) k *
  field_at sh t_kp (DOT I._rcu) (Vint Int.zero) k *
  field_at sh t_kp (DOT I._internal_id) (Vlong Int64.zero) k *
  prot3_zero_kp_pad sh k.
Proof.
  rewrite prot3_zero_kp_zero_val_eq. unfold prot3_zero_kp_zero_val.
  unfold_data_at (data_at _ _ _ _).
  unfold prot3_zero_kp_pad, spacer, at_offset, symkey_val, prot3_zero_sym0, entry_val.
  cbn [sk_key sk_birth sk_valid e_peer e_type e_index].
  repeat match goal with |- context [Z.eq_dec ?a ?b] => destruct (Z.eq_dec a b); [lia|] end.
  change (1184 - 1181) with 3.
  cancel.
Qed.

Lemma prot3_zero_kp_entry_field sh k v :
  field_compatible t_kp [] k ->
  field_at sh t_kp (DOT I._entry) v k = data_at sh t_entry_s v k.
Proof.
  intros FC. rewrite field_at_data_at. unfold field_address. rewrite if_true by auto with field_compatible.
  simpl nested_field_offset. rewrite isptr_offset_val_zero by auto with field_compatible. reflexivity.
Qed.

(* noise.c's globals: keypair_counter apart from the rest (the rest holds BLAKE2s constants: kept folded) *)
Definition prot3_zero_ng_rest (gv: globals) : mpred :=
  !! (Zlength init_hash = 32 /\ Zlength init_ck = 32) &&
  (data_at Ers (tarray tuchar 37) (bytes handshake_name) (gv I._handshake_name) *
   data_at Ers (tarray tuchar 34) (bytes identifier_name) (gv I._identifier_name) *
   data_at Ews (tarray tuchar 32) (bytes init_hash) (gv I._handshake_init_hash) *
   data_at Ews (tarray tuchar 32) (bytes init_ck) (gv I._handshake_init_chaining_key) *
   data_at Ews (tarray tuchar 32) (bytes zeros32) (gv I._zero_point)).

Lemma prot3_zero_ng_split gv kc :
  noise_globals gv kc = data_at Ews t_atomic64 (Vlong kc) (gv I._keypair_counter) * prot3_zero_ng_rest gv.
Proof.
  unfold noise_globals, noise_globals_raw, prot3_zero_ng_rest.
  remember init_hash as IH eqn:EIH. remember init_ck as IC eqn:EIC.
  remember handshake_name as HN eqn:EHN. remember identifier_name as IN eqn:EIN.
  clear EIH EIC EHN EIN.
  apply pred_ext; Intros; entailer!.
Qed.

End HSZero.

Section Zero.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

Local Open Scope logic.

Definition Gz (cs: compspecs) := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw cs.

Lemma prot3_zero_cookie_zero sh c :
  @data_at Noise.CS sh t_cookie (zero_val t_cookie) c |-- cookie_rep sh c cookie_zero.
Proof.
  unfold cookie_rep. apply andp_right.
  { apply prop_right. unfold cookie_ok, cookie_zero, zeros.
    cbn [ck_cookie ck_last_mac1 ck_dkey ck_mkey]. rewrite !Zlength_Zrepeat by lia. auto. }
  Exists (Vint Int.zero).
  apply derives_refl'. f_equal. apply JMeq_eq. eapply JMeq_trans; [apply JMeq_zero_val_zero_val' |].
  apply JMeq_refl.
Qed.

Lemma prot3_zero_body_cookie_init :
  @semax_body (QPvarspecs Cookie.qp) (Gz Cookie.CS) Cookie.CS
    WgNoise.cookie.code.f_wg_cookie_init wg_cookie_init_spec.
Proof.
  start_function.
  assert_PROP (@field_compatible Noise.CS t_cookie [] c) as FC by entailer!.
  sep_apply (@prot3_zero_data_at__bytes Noise.CS Cookie.CS sh t_cookie c).
  change (@sizeof Noise.CS t_cookie) with 112.
  forward_call (sh, c, 0, 112).
  sep_apply (@prot3_zero_bytes_struct Noise.CS Cookie.CS sh t_cookie c); auto.
  sep_apply (prot3_zero_cookie_zero sh c).
  entailer!.
Qed.

Section HSInit.
#[local] Existing Instance Noise.CS.
Definition Gn := Gz Noise.CS.

Lemma prot3_zero_body_hs_init :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_init (wg_noise_handshake_init_spec x25519).
Proof.
  start_function.
  assert_PROP (field_compatible t_hs [] (hs_addr p)) as FCh by entailer!.
  sep_apply (@prot3_zero_data_at__bytes Noise.CS Noise.CS sh t_hs (hs_addr p)).
  change (@sizeof Noise.CS t_hs) with 304.
  forward_call (sh, hs_addr p, 0, 304).
  sep_apply (@prot3_zero_bytes_struct Noise.CS Noise.CS sh t_hs (hs_addr p)); auto.
  sep_apply (prot3_zero_hs_split sh (hs_addr p)).
  unfold hs_rep, entry_val, prot3_zero_HZ. Intros lk. unfold t_hs.
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
         wg_consts gv)).
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
  sep_apply (prot3_zero_hs_fold sh (hs_addr p) H1' lk Hok).
  forward_call (gv, sh, p, H1', shi, ID).
  { change (hs_sid H1') with sid. cancel. }
  change (hs_sid H1') with sid.
  replace (hs_set_ss H1' (precomputed x25519 ID (hs_rstatic H1'))) with (hs_initial x25519 ID sid pub psk')
    by reflexivity.
  unfold entry_out, entry_at, entry_val. cbn [e_peer e_type e_index].
  rewrite <- prot3_zero_entry_field by auto. unfold bytes_at. rewrite H0.
  entailer!.
  apply derives_refl.
Qed.

Lemma prot3_zero_bytes_zeros_eq sh n p : 0 <= n ->
  bytes_at sh (zeros n) p = data_at sh (tarray tuchar n) (Zrepeat (Vubyte Byte.zero) n) p.
Proof.
  intros. unfold bytes_at, bytes, zeros. rewrite Zlength_Zrepeat by lia.
  unfold Zrepeat. rewrite map_repeat. reflexivity.
Qed.

Lemma prot3_zero_body_kp_create :
  @semax_body (QPvarspecs Noise.qp) Gn Noise.CS WgNoise.noise.code.f_keypair_create (keypair_create_spec CSw).
Proof.
  start_function.
  forward_call (gv, S, 1200, Int.zero).
  Intros k.
  forward_if (k <> nullval).
  { destruct (eq_dec k nullval); [subst; entailer! | unfold bytes_at; entailer!]. }
  { subst k. forward. Exists nullval. rewrite !if_true by auto. entailer!. }
  { forward. entailer!. }
  Intros. rewrite !if_false by auto. Intros.
  rewrite prot3_zero_bytes_zeros_eq by lia.
  assert_PROP (malloc_compatible 1200 k) as MC.
  { sep_apply (@malloc_token_local_facts CSw Ews (tarray tuchar 1200) k). entailer!. }
  assert (FC: field_compatible t_kp [] k).
  { apply malloc_compatible_field_compatible; [exact MC | reflexivity | reflexivity]. }
  sep_apply (@prot3_zero_bytes_struct Noise.CS Noise.CS Ews t_kp k); auto.
  sep_apply (prot3_zero_kp_split Ews k).
  rewrite prot3_zero_ng_split. Intros. unfold t_atomic64, t_kp.
  forward. forward.
  forward. forward. forward. forward. forward. forward.
  Exists k. rewrite if_false by auto. rewrite prot3_zero_ng_split.
  unfold keypair_rep, entry_out, entry_at, entry_val, kp_fresh, symkey_val, prot3_zero_sym0.
  cbn [e_peer e_type e_index sk_key sk_birth sk_valid kp_send kp_scounter kp_recv kp_rcounter kp_backtrack
       kp_rindex kp_init kp_refs kp_id fst snd].
  rewrite <- prot3_zero_kp_entry_field by auto.
  Intros. Exists (Vint Int.zero) (Vint Int.zero).
  entailer!.
  { unfold kp_ok, zeros. cbn [sk_key kp_send kp_recv kp_backtrack]. rewrite !Zlength_Zrepeat by lia. auto. }
  unfold prot3_zero_kp_pad. apply derives_refl.
Qed.

End HSInit.

End Zero.

Theorem prot_bodies3_zero :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_wg_noise_handshake_init (wg_noise_handshake_init_spec x25519)) /\
  (@semax_body (QPvarspecs Noise.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Noise.CS) Noise.CS
      WgNoise.noise.code.f_keypair_create (keypair_create_spec CSw)) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_init wg_cookie_init_spec).
Proof.
  intros. split; [|split].
  - apply prot3_zero_body_hs_init.
  - apply prot3_zero_body_kp_create.
  - apply prot3_zero_body_cookie_init.
Qed.
