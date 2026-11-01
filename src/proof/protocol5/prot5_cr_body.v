(* The body of wg_noise_handshake_create_response against its v5 specification (prot_specs5.v), in the
   context Gprot5: v4's script (prot4_cr_body.v) over the v5 representation.  The message buffer is a message
   (Some M) or uninitialised (None); the proof runs once over the values its five written fields hold
   (cr5_hdr .. cr5_encn: the message's, or undefined), and each exit reassembles the buffer with cr5_exit. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol4.prot4_cr_body.
Require Import WgNoise.proof.protocol5.prot_prog5.
Require WgNoise.noise.code WgNoise.shim.code.
Require WgNoise.proof.protocol.prot_body3_shim_table1.

Section CreateResp5.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.
Context (HX: x25519_props x25519) (HA: aead_props aead_enc aead_dec).

#[local] Existing Instance Noise.CS.
Local Open Scope logic.

Definition Gn5 := Gprot5 x25519 aead_enc aead_dec CSw Noise.CS.

(* the values the buffer's header, sender, receiver, ephemeral and encrypted_nothing fields hold before the
   call: the message's for Some M, undefined for None *)
Definition cr5_hdr (Mo: option resp_msg) : val := match Mo with Some M => Vint (rm_type M) | None => Vundef end.
Definition cr5_snd (Mo: option resp_msg) : val := match Mo with Some M => Vint (rm_sender M) | None => Vundef end.
Definition cr5_rcv (Mo: option resp_msg) : val := match Mo with Some M => Vint (rm_receiver M) | None => Vundef end.
Definition cr5_eph (Mo: option resp_msg) : list val :=
  match Mo with Some M => bytes (rm_eph M) | None => Zrepeat Vundef 32 end.
Definition cr5_encn (Mo: option resp_msg) : list val :=
  match Mo with Some M => bytes (rm_encn M) | None => Zrepeat Vundef 16 end.

(* the buffer field by field, with arbitrary values in the five fields create_response writes *)
Definition cr5_msg (sh: share) (m: val) (hv sv rv: val) (ev nv: list val) : mpred :=
  field_at sh t_resp (DOT N._header) hv m *
  field_at sh t_resp (DOT N._sender_index) sv m *
  field_at sh t_resp (DOT N._receiver_index) rv m *
  field_at sh t_resp (DOT N._unencrypted_ephemeral) ev m *
  field_at sh t_resp (DOT N._encrypted_nothing) nv m *
  field_at_ sh t_resp (DOT N._macs) m.

Definition cr5_ok (Mo: option resp_msg) : Prop := match Mo with Some M => rm_ok5 M | None => True end.

Lemma cr5_pre sh m Mo :
  resp_opt_rep sh m Mo |--
  !! (cr5_ok Mo /\ field_compatible t_resp [] m) &&
  cr5_msg sh m (cr5_hdr Mo) (cr5_snd Mo) (cr5_rcv Mo) (cr5_eph Mo) (cr5_encn Mo).
Proof.
  destruct Mo as [M|]; unfold resp_opt_rep, cr5_msg, cr5_ok.
  - unfold resp_rep5. Intros. cbn [cr5_hdr cr5_snd cr5_rcv cr5_eph cr5_encn]. entailer!.
    apply field_compatible_cons in H0. destruct H0; auto.
  - unfold_data_at (data_at_ sh t_resp m). entailer!.
    apply field_compatible_cons in H. destruct H; auto.
Qed.

Lemma cr5_eph_len Mo : cr5_ok Mo -> Zlength (cr5_eph Mo) = 32.
Proof. destruct Mo as [M|]; cbn; [intros [L _]; unfold bytes; rewrite Zlength_map; exact L | reflexivity]. Qed.

(* the buffer after an exit with result ok and model message M': the values in its fields are M''s when
   the buffer is a message afterwards (opt_after) *)
Lemma cr5_exit sh m Mo ok M' hv sv rv ev nv :
  match opt_after ok Mo M' with
  | Some M'' => rm_ok5 M'' /\ hv = Vint (rm_type M'') /\ sv = Vint (rm_sender M'') /\
                rv = Vint (rm_receiver M'') /\ ev = bytes (rm_eph M'') /\ nv = bytes (rm_encn M'')
  | None => True end ->
  cr5_msg sh m hv sv rv ev nv |-- resp_opt_rep sh m (opt_after ok Mo M').
Proof.
  intros H. unfold cr5_msg. destruct (opt_after ok Mo M') as [M''|]; unfold resp_opt_rep.
  - destruct H as (OK & -> & -> & -> & -> & ->). unfold resp_rep5. entailer!.
  - unfold_data_at (data_at_ sh t_resp m).
    sep_apply (field_at_field_at_ sh t_resp (DOT N._header) hv m).
    sep_apply (field_at_field_at_ sh t_resp (DOT N._sender_index) sv m).
    sep_apply (field_at_field_at_ sh t_resp (DOT N._receiver_index) rv m).
    sep_apply (field_at_field_at_ sh t_resp (DOT N._unencrypted_ephemeral) ev m).
    sep_apply (field_at_field_at_ sh t_resp (DOT N._encrypted_nothing) nv m).
    unfold field_at_. entailer!.
Qed.

(* the exit before any write: the buffer as it was *)
Lemma cr5_exit_same sh m Mo : cr5_ok Mo ->
  cr5_msg sh m (cr5_hdr Mo) (cr5_snd Mo) (cr5_rcv Mo) (cr5_eph Mo) (cr5_encn Mo) |--
  resp_opt_rep sh m (opt_after false Mo (resp_of Mo)).
Proof. intros OK. apply cr5_exit. destruct Mo as [M|]; cbn; auto. exact (conj OK (conj eq_refl (conj eq_refl (conj eq_refl (conj eq_refl eq_refl))))). Qed.

(* a failing exit after the header, receiver and maybe the ephemeral were written: the model's message
   keeps the sender and encrypted_nothing; the buffer is uninitialised again if it was *)
Lemma cr5_exit_fail sh m Mo t rcv e ev : cr5_ok Mo ->
  (forall M, Mo = Some M -> ev = bytes e /\ Zlength e = 32) ->
  cr5_msg sh m (Vint t) (cr5_snd Mo) (Vint rcv) ev (cr5_encn Mo) |--
  resp_opt_rep sh m (opt_after false Mo (mkRM t (rm_sender (resp_of Mo)) rcv e (rm_encn (resp_of Mo))
                                          (rm_mac1 (resp_of Mo)) (rm_mac2 (resp_of Mo)))).
Proof.
  intros OK HE. apply cr5_exit. destruct Mo as [M|]; cbn; auto.
  destruct (HE M eq_refl) as [-> L]. destruct OK as [_ L2]. unfold rm_ok5. cbn. auto 10.
Qed.

(* the successful exit: every represented field written *)
Lemma cr5_exit_ok sh m Mo t snd rcv e n a b : Zlength e = 32 -> Zlength n = 16 ->
  cr5_msg sh m (Vint t) (Vint snd) (Vint rcv) (bytes e) (bytes n) |--
  resp_opt_rep sh m (opt_after true Mo (mkRM t snd rcv e n a b)).
Proof. intros L1 L2. apply cr5_exit. cbn. unfold rm_ok5. cbn. auto 10. Qed.

Lemma cr5_eph_eq sh m ev :
  field_at sh t_resp (DOT N._unencrypted_ephemeral) ev m =
  data_at sh (tarray tuchar 32) ev (field_address t_resp (DOT N._unencrypted_ephemeral) m).
Proof. rewrite field_at_data_at. reflexivity. Qed.

Lemma cr5_encn_eq sh m nv :
  field_at sh t_resp (DOT N._encrypted_nothing) nv m =
  data_at sh (tarray tuchar 16) nv (field_address t_resp (DOT N._encrypted_nothing) m).
Proof. rewrite field_at_data_at. reflexivity. Qed.

(* the peer without its device field and handshake (peer_rep5) *)
Definition cr5_prest (sh: share) (p: val) (P: peer) : mpred :=
  field_at sh t_peer (DOT I._is_dead) (Val.of_bool (p_dead P)) p *
  kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
  field_at_ sh t_peer (DOT I._last_sent_handshake) p *
  field_at_ sh t_peer (DOT I._latest_cookie) p *
  field_at sh t_peer (DOT I._refcount) (Vint (p_refs P)) p *
  field_at_ sh t_peer (DOT I._internal_id) p *
  field_at sh t_peer (DOT I._pubkey_next) (p_pknext P) p *
  spacer sh 9 16 p * spacer sh 476 480 p.

Lemma cr5_peer_eq sh p P :
  peer_rep5 sh p P =
  !! field_compatible t_peer [] p &&
  (field_at sh t_peer (DOT I._device) (p_device P) p * cr5_prest sh p P * hs_rep sh (hs_addr p) (p_hs P)).
Proof. unfold peer_rep5, cr5_prest. f_equal. apply pred_ext; cancel. Qed.

Lemma cr5_prest_set sh p P H : cr5_prest sh p (p_set_hs P H) = cr5_prest sh p P.
Proof. reflexivity. Qed.

Lemma cr5_consts gv :
  spec.blake2s_globals gv * curve25519_globals gv * zero_page gv |-- wg_consts5 gv.
Proof. unfold wg_consts5. cancel. Qed.

Ltac cr5_arg ep rsp rep pskp hp ckp mep mnp := apply prop_right; unfold ep, rsp, rep, pskp, hp, ckp, mep, mnp; simpl;
  rewrite ?field_address_offset by auto with field_compatible; reflexivity.

Ltac cr5_len HX HA :=
  match goal with
  | |- Zlength (kdf1 _ _) = _ => apply prot4_cr_kdf1_len
  | |- Zlength (kdf2 _ _) = _ => apply prot4_cr_kdf2_len
  | |- Zlength (kdf3 _ _) = _ => apply prot4_cr_kdf3_len
  | |- Zlength (mix_hash _ _) = _ => apply prot4_cr_mix_hash_len
  | |- Zlength (x25519 _ _) = _ => apply HX
  | |- Zlength (clamp _) = _ => unfold clamp; list_solve
  | |- Zlength (aead_enc _ _ _ []) = _ => rewrite (aead_enc_length _ _ HA); reflexivity
  | H: Zlength ?x = ?n |- Zlength ?x = ?n => exact H
  end.

(* the peer and its handshake in the postcondition, field by field as in the proof *)
Ltac cr5_fold HX HA :=
  rewrite cr5_peer_eq, prot4_cr_hs_eq, cr5_prest_set;
  cbn [p_hs p_device p_set_hs hs_set_eph hs_set_ckh hs_set_state hs_state hs_lic hs_sid hs_eph hs_rstatic
       hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex fst snd];
  rewrite prot4_cr_hs_ephemeral_private by cr5_len HX HA;
  rewrite prot4_cr_hs_remote_static by cr5_len HX HA;
  rewrite prot4_cr_hs_remote_ephemeral by cr5_len HX HA;
  rewrite prot4_cr_hs_preshared_key by cr5_len HX HA;
  rewrite prot4_cr_hs_hash by cr5_len HX HA;
  rewrite prot4_cr_hs_chaining_key by cr5_len HX HA;
  unfold wg_consts5.

Ltac cr5_ok HX HA := unfold hs_ok;
  cbn [p_hs p_device p_set_hs hs_set_eph hs_set_ckh hs_set_state hs_state hs_lic hs_sid hs_eph hs_rstatic
       hs_reph hs_ss hs_psk hs_hash hs_ck hs_ts hs_rindex fst snd];
  repeat split; cr5_len HX HA.

(* sep_apply an exit lemma (cr5_exit, cr5_exit_same) to the buffer's fields *)
Ltac cr5_exit_with L := let X := fresh "X" in pose proof L as X; unfold cr5_msg in X; sep_apply X; clear X.

Ltac cr5_nn := repeat match goal with |- context [eq_dec nullval nullval] =>
  let NN := fresh "NN" in destruct (eq_dec nullval nullval) as [_|NN]; [|congruence] end.

Lemma prot5_cr_body :
  @semax_body (QPvarspecs Noise.qp) Gn5 Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_create_response (wg_noise_handshake_create_response_spec x25519 aead_enc).
Proof.
  start_function.
  forward.
  forward_loop
    (PROP () LOCAL (temp N._ret (Val.of_bool false); lvar N._key (tarray tuchar 32) v_key; gvars gv;
                    temp N._dst m; temp N._handshake (hs_addr p))
     SEP (data_at_ Tsh (tarray tuchar 32) v_key; resp_opt_rep shm m Mo; peer_rep5 shp p P; device_rep5 shd wg D;
          itable sht (d_itab D) T; shim_state4 gv S w; wg_consts5 gv))
  continue: (EX r: list byte, EX idx: int,
     PROP (Zlength r = 32; fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) = true -> t_fresh T (hs_addr p) idx)
     LOCAL (temp N._ret (Val.of_bool (fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))));
            lvar N._key (tarray tuchar 32) v_key; gvars gv)
     SEP (data_at_ Tsh (tarray tuchar 32) v_key;
          resp_opt_rep shm m (opt_after (fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))) Mo
                                       (snd (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))));
          peer_rep5 shp p (p_set_hs P (snd (cr_res x25519 aead_enc P (resp_of Mo) r idx)));
          device_rep5 shd wg D;
          itable sht (d_itab D) (if fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) then t_insert T (hs_addr p) idx else T);
          shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                         then (if fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) then shim_u32 (shim_draw S r) idx
                               else shim_draw S r)
                         else S) w;
          wg_consts5 gv))%assert
  break: (EX r: list byte, EX idx: int,
     PROP (Zlength r = 32; fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) = true -> t_fresh T (hs_addr p) idx)
     LOCAL (temp N._ret (Val.of_bool (fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))));
            lvar N._key (tarray tuchar 32) v_key; gvars gv)
     SEP (data_at_ Tsh (tarray tuchar 32) v_key;
          resp_opt_rep shm m (opt_after (fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))) Mo
                                       (snd (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))));
          peer_rep5 shp p (p_set_hs P (snd (cr_res x25519 aead_enc P (resp_of Mo) r idx)));
          device_rep5 shd wg D;
          itable sht (d_itab D) (if fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) then t_insert T (hs_addr p) idx else T);
          shim_state4 gv (if Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION
                         then (if fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx)) then shim_u32 (shim_draw S r) idx
                               else shim_draw S r)
                         else S) w;
          wg_consts5 gv))%assert.
  { entailer!. }
  2: { Intros r idx. forward. Exists r idx. entailer!. }
  2: { Intros r idx. forward_call (Tsh, v_key, 32).
       forward. Exists r idx. entailer!.
       destruct (fst (fst (cr_res x25519 aead_enc P (resp_of Mo) r idx))); reflexivity. }
  sep_apply (cr5_pre shm m Mo). rewrite cr5_peer_eq, prot4_cr_hs_eq. Intros. unfold cr5_msg. Intros.
  forward.
  forward_if.
  { forward. Exists zeros32 Int.zero.
    assert (Hs: Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION = false).
    { apply Int.eq_false. intro E. rewrite E in H5. contradiction. }
    unfold cr_res, prot_specs4.cr_res. rewrite (prot4_cr_m0 _ _ _ _ _ _ Hs), Hs. cbn [fst snd].
    cr5_exit_with (cr5_exit_same shm m Mo H1).
    rewrite cr5_peer_eq, prot4_cr_hs_eq, cr5_prest_set.
    cbn [p_hs p_device p_set_hs]. entailer!. }
  assert (Hs: Int.eq (hs_state (p_hs P)) HS_CONSUMED_INITIATION = true).
  { rewrite H5. reflexivity. }
  forward. forward. forward.
  assert_PROP (field_compatible t_hs (DOT I._ephemeral_private) (hs_addr p)) as FCe by entailer!.
  destruct H4 as (Leph & Lrs & Lreph & Lss & Lpsk & Lhash & Lck & Lts).
  pose proof (cr5_eph_len Mo H1) as Lmeph.
  rewrite (prot4_cr_hs_ephemeral_private shp _ _ Leph), (prot4_cr_hs_remote_static shp _ _ Lrs),
    (prot4_cr_hs_remote_ephemeral shp _ _ Lreph), (prot4_cr_hs_preshared_key shp _ _ Lpsk),
    (prot4_cr_hs_hash shp _ _ Lhash), (prot4_cr_hs_chaining_key shp _ _ Lck),
    (cr5_eph_eq shm m).
  set (ep := field_address t_hs (DOT I._ephemeral_private) (hs_addr p)).
  set (rsp := field_address t_hs (DOT I._remote_static) (hs_addr p)).
  set (rep := field_address t_hs (DOT I._remote_ephemeral) (hs_addr p)).
  set (pskp := field_address t_hs (DOT I._preshared_key) (hs_addr p)).
  set (hp := field_address t_hs (DOT I._hash) (hs_addr p)).
  set (ckp := field_address t_hs (DOT I._chaining_key) (hs_addr p)).
  set (mep := field_address t_resp (DOT N._unencrypted_ephemeral) m).
  set (mnp := field_address t_resp (DOT N._encrypted_nothing) m).
  sep_apply (prot4_cr_bytes_ shp (hs_eph (p_hs P)) ep Leph).
  assert (FCh: field_compatible t_hs [] (hs_addr p)).
  { apply field_compatible_cons in FCe. destruct FCe; auto. }
  forward_call (gv, S, w, shp, ep).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  Intros r.
  assert (Lcl: Zlength (clamp r) = 32) by (unfold clamp; list_solve).
  rewrite (prot4_cr_bytes32 shp (clamp r) ep Lcl).
  unfold wg_consts5.
  forward_call (shm, mep, cr5_eph Mo, shp, ep, clamp r, gv).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  { cancel. }
  destruct (andb (memneq_bool (clamp r) zeros32) (memneq_bool (x25519 (clamp r) basepoint9) zeros32)) eqn:Hgp.
  2: { forward_if.
       2: { exfalso. apply H6. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res, prot_specs4.cr_res. rewrite (prot4_cr_m1 _ _ _ _ _ _ Hs Hgp), Hs. cbn [fst snd].
       rewrite <- (prot4_cr_bytes32 shp (clamp r) ep Lcl).
       subst ep rsp rep pskp hp ckp mep mnp.
       rewrite <- (cr5_eph_eq shm m).
       cr5_exit_with (cr5_exit_fail shm m Mo (Int.repr 2) (hs_rindex (p_hs P))
         (if memneq_bool (clamp r) zeros32 then x25519 (clamp r) basepoint9 else rm_eph (resp_of Mo))
         (if memneq_bool (clamp r) zeros32 then map Vubyte (x25519 (clamp r) basepoint9) else cr5_eph Mo) H1
         ltac:(intros M0 ->; destruct (memneq_bool (clamp r) zeros32);
               [split; [reflexivity|apply HX] | split; [reflexivity|exact (proj1 H1)]])).
       cr5_fold HX HA.
       entailer!. cr5_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H6. }
  apply andb_prop in Hgp. destruct Hgp as [Hm1 Hm2]. rewrite Hm1.
  assert (LE: Zlength (x25519 (clamp r) basepoint9) = 32) by apply HX.
  rewrite <- (prot4_cr_bytes32 shm _ mep LE), <- (prot4_cr_bytes32 shp (clamp r) ep Lcl).
  sep_apply (cr5_consts gv).
  forward_call (gv, true, shm, mep, shm, mep, x25519 (clamp r) basepoint9, shp, ckp, hs_ck (p_hs P), shp, hp,
                hs_hash (p_hs P)).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  set (E := x25519 (clamp r) basepoint9) in *.
  forward_call (gv, shp, ckp, kdf1 (hs_ck (p_hs P)) E, shp, nullval, shp, ep, clamp r, shp, rep, hs_reph (p_hs P)).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  { cr5_nn. cancel. }
  cr5_nn.
  destruct (dh_ok x25519 (clamp r) (hs_reph (p_hs P))) eqn:Hd1.
  2: { forward_if.
       2: { exfalso. apply H7. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res, prot_specs4.cr_res. rewrite (prot4_cr_m2 _ _ (p_hs P) (resp_of Mo) r Int.zero Hs Hm1 Hm2 Hd1), Hs.
       cbn [fst snd].
       rewrite (prot4_cr_bytes32' shm E mep LE).
       subst ep rsp rep pskp hp ckp mep mnp.
       rewrite <- (cr5_eph_eq shm m).
       cr5_exit_with (cr5_exit_fail shm m Mo (Int.repr 2) (hs_rindex (p_hs P)) E (bytes E) H1
         ltac:(intros M0 _; split; [reflexivity|exact LE])).
       subst E. cr5_fold HX HA.
       entailer!. cr5_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H7. }
  forward_call (gv, shp, ckp, kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))), shp, nullval,
                shp, ep, clamp r, shp, rsp, hs_rstatic (p_hs P)).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  { cr5_nn. cancel. }
  cr5_nn.
  destruct (dh_ok x25519 (clamp r) (hs_rstatic (p_hs P))) eqn:Hd2.
  2: { forward_if.
       2: { exfalso. apply H8. reflexivity. }
       forward.
       Exists r Int.zero.
       unfold cr_res, prot_specs4.cr_res. rewrite (prot4_cr_m3 _ _ (p_hs P) (resp_of Mo) r Int.zero Hs Hm1 Hm2 Hd1 Hd2), Hs.
       cbn [fst snd].
       rewrite (prot4_cr_bytes32' shm E mep LE).
       subst ep rsp rep pskp hp ckp mep mnp.
       rewrite <- (cr5_eph_eq shm m).
       cr5_exit_with (cr5_exit_fail shm m Mo (Int.repr 2) (hs_rindex (p_hs P)) E (bytes E) H1
         ltac:(intros M0 _; split; [reflexivity|exact LE])).
       subst E. cr5_fold HX HA.
       entailer!. cr5_ok HX HA. }
  forward_if.
  { exfalso. apply Int.one_not_zero. exact H8. }
  forward_call (gv, shp, ckp, kdf1 (kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))))
                                  (x25519 (clamp r) (hs_rstatic (p_hs P))),
                shp, hp, mix_hash (hs_hash (p_hs P)) E, Tsh, v_key, shp, pskp, hs_psk (p_hs P)).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  set (ck3 := kdf1 (kdf1 (kdf1 (hs_ck (p_hs P)) E) (x25519 (clamp r) (hs_reph (p_hs P))))
                   (x25519 (clamp r) (hs_rstatic (p_hs P)))) in *.
  set (h2 := mix_hash (mix_hash (hs_hash (p_hs P)) E) (kdf2 ck3 (hs_psk (p_hs P)))) in *.
  rewrite (cr5_encn_eq shm m (cr5_encn Mo)). fold mnp.
  sep_apply (data_at_data_at_ shm (tarray tuchar 16) (cr5_encn Mo) mnp).
  forward_call (gv, shm, mnp, Tsh, nullval, @nil byte, Tsh, v_key, kdf3 ck3 (hs_psk (p_hs P)), shp, hp, h2).
  { cr5_arg ep rsp rep pskp hp ckp mep mnp. }
  { rewrite prot4_cr_prim_nil. cancel. }
  { rewrite Zlength_nil. rep_lia. }
  rewrite prot4_cr_prim_nil.
  change (Zlength (@nil byte) + 16) with 16.
  destruct H0 as [Ee [HEe HEp]].
  assert (HIn: In (hs_addr p) (saddrs (t_D T))).
  { unfold t_entry in HEe. destruct (sfind (t_D T) (hs_addr p)) as [[she0 E0]|] eqn:HS; inv HEe.
    eapply WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_saddrs_in. apply WgNoise.proof.protocol.prot_body3_shim_table1.prot3_shim_table1_sfind_In. exact HS. }
  sep_apply (prot4_cr_open sht (d_itab D) T (hs_addr p) Ee HEe FCh). Intros she.
  unfold entry_val.
  forward.
  rewrite HEp.
  sep_apply (modus_ponens_wand (field_at she t_hs (DOT N._entry)
     (p, (succ_in (t_L T) (hs_addr p), (Val.of_bool (vin (hs_addr p) (t_L T)), (Vint (e_type Ee), Vint (e_index Ee)))))
     (hs_addr p)) (itable sht (d_itab D) T)).
  forward.
  { rewrite H. unfold device_rep5. Intros. entailer!. }
  rewrite H.
  unfold device_rep5. Intros.
  forward.
  { unfold itable. Intros. entailer!. }
  forward_call (gv, shim_draw S r, w, sht, d_itab D, T, hs_addr p, @None (share * entry)).
    { change (prot_specs4.raw_rep (hs_addr p) None) with emp. rewrite emp_sepcon. cancel. }
  all: try (change (prot_specs4.raw_ok T (hs_addr p) None) with (In (hs_addr p) (saddrs (t_D T))); auto).
  change (prot_specs4.raw_add T (hs_addr p) None) with T. Intros idx.
  forward. forward. forward.
  Exists r idx.
  pose proof (prot4_cr_m4 x25519 aead_enc (p_hs P) (resp_of Mo) r idx Hs Hm1 Hm2 Hd1 Hd2) as Hmod. cbv zeta in Hmod.
  unfold cr_res, prot_specs4.cr_res. rewrite Hmod, Hs. cbn [fst snd].
  sep_apply (prot4_cr_bytes_ Tsh (kdf3 ck3 (hs_psk (p_hs P))) v_key (prot4_cr_kdf3_len _ _)).
  rewrite (prot4_cr_bytes32' shm E mep LE).
  subst ep rsp rep pskp hp ckp mep mnp.
  rewrite <- (cr5_eph_eq shm m), <- (cr5_encn_eq shm m).
  cr5_exit_with (cr5_exit_ok shm m Mo (Int.repr 2) idx (hs_rindex (p_hs P)) E (aead_enc (kdf3 ck3 (hs_psk (p_hs P))) 0 h2 [])
    (rm_mac1 (resp_of Mo)) (rm_mac2 (resp_of Mo)) LE ltac:(rewrite (aead_enc_length _ _ HA); reflexivity)).
  subst E ck3 h2. cr5_fold HX HA.
  unfold device_rep5.
  entailer!. cr5_ok HX HA.
Qed.

End CreateResp5.

Theorem prot5_cr_bodies :
  forall x25519 aead_enc aead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  @semax_body (QPvarspecs Noise.qp) (Gprot5 x25519 aead_enc aead_dec CSw Noise.CS) Noise.CS
    WgNoise.noise.code.f_wg_noise_handshake_create_response (wg_noise_handshake_create_response_spec x25519 aead_enc).
Proof.
  intros. eapply prot5_cr_body; eauto.
Qed.
