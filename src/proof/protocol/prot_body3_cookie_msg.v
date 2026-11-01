(* Body proofs of the protocol piece, group cookie_msg.
   Target: prot_bodies3_cookie_msg.  Prove each function's body against its specification (prot_specs3.v) in the
   compspecs of its unit, with the context Gprot3 (prot_prog3.v). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_prog3.
Require Import WgNoise.proof.blake2s.model WgNoise.proof.blake2s.spec WgNoise.proof.blake2s.b2s_spec3.
Require Import WgNoise.proof.protocol.prot3_cookie_msg_lib.
Require WgNoise.noise.code WgNoise.cookie.code WgNoise.shim.code.

Section CookieMsg.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).
Variable CSw: compspecs.

#[local] Existing Instance Cookie.CS.

Definition prot3_cookie_msg_G := Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS.

Lemma prot3_cookie_msg_fc_peer p :
  @field_compatible Noise.CS t_peer [] p -> @field_compatible Cookie.CS t_peer [] p.
Proof.
  intros FC.
  assert (E: cs_preserve_type Noise.CS Cookie.CS (coeq Noise.CS Cookie.CS) t_peer = true) by (vm_compute; reflexivity).
  apply (proj1 (@field_compatible_change_composite Noise.CS Cookie.CS _ t_peer E [] p)). exact FC.
Qed.

Lemma prot3_cookie_msg_cookie_eq sh p C lk :
  @field_compatible Cookie.CS t_peer [] p ->
  @data_at Noise.CS sh t_cookie (cookie_val C lk) (cookie_addr p) =
  @field_at Cookie.CS sh t_peer (DOT C._latest_cookie) (cookie_val C lk) p.
Proof.
  intros FC.
  rewrite (field_at_data_at sh t_peer (DOT C._latest_cookie)).
  rewrite field_address_offset by auto with field_compatible.
  apply data_at_cs_eq; [apply JMeq_refl | reflexivity].
Qed.

Lemma prot3_cookie_msg_fa_mkey sh l p : Zlength l = 32 ->
  @field_at Cookie.CS sh t_peer (DOT C._latest_cookie DOT C._message_mac1_key) (bytes l) p =
  bytes_at sh l (field_address t_peer (DOT C._latest_cookie DOT C._message_mac1_key) p).
Proof. intros E. rewrite field_at_data_at. unfold bytes_at. rewrite E. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_cookie_msg_fa_cookie sh l p : Zlength l = 16 ->
  @field_at Cookie.CS sh t_peer (DOT C._latest_cookie DOT C._cookie) (bytes l) p =
  bytes_at sh l (field_address t_peer (DOT C._latest_cookie DOT C._cookie) p).
Proof. intros E. rewrite field_at_data_at. unfold bytes_at. rewrite E. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_cookie_msg_fa_last sh l p : Zlength l = 16 ->
  @field_at Cookie.CS sh t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) (bytes l) p =
  @data_at Cookie.CS sh (tarray tuchar 16) (bytes l) (field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p).
Proof. intros E. rewrite field_at_data_at. reflexivity. Qed.

Lemma prot3_cookie_msg_msg1 (msg m1: list byte) :
  32 <= Zlength msg -> Zlength m1 = 16 ->
  let n := Zlength msg in
  let msg1 := sublist 0 (n - 32) msg ++ m1 ++ sublist (n - 16) n msg in
  Zlength msg1 = n /\ sublist 0 (n - 32) msg1 = sublist 0 (n - 32) msg /\
  sublist (n - 32) (n - 16) msg1 = m1 /\ sublist (n - 16) n msg1 = sublist (n - 16) n msg.
Proof. intros H1 H2 n msg1. subst n msg1. split; [|split; [|split]]; list_solve. Qed.

Lemma prot3_cookie_msg_model Ck msg now m1 :
  m1 = MAC (ck_mkey Ck) (sublist 0 (Zlength msg - 32) msg) ->
  Zlength (sublist 0 (Zlength msg - 32) msg ++ m1 ++ sublist (Zlength msg - 16) (Zlength msg) msg) = Zlength msg ->
  add_mac_model Ck msg now =
  (sublist 0 (Zlength msg - 16) (sublist 0 (Zlength msg - 32) msg ++ m1 ++ sublist (Zlength msg - 16) (Zlength msg) msg) ++
     (if andb (ck_valid Ck) (negb (birthdate_expired (ck_birth Ck) (Int64.repr 115) now))
      then MAC (ck_cookie Ck) (sublist 0 (Zlength msg - 16)
             (sublist 0 (Zlength msg - 32) msg ++ m1 ++ sublist (Zlength msg - 16) (Zlength msg) msg))
      else zeros 16),
   mkCookie (ck_birth Ck) (ck_valid Ck) (ck_cookie Ck) true m1 (ck_dkey Ck) (ck_mkey Ck)).
Proof.
  intros E L. unfold add_mac_model. cbv zeta. unfold mac1_of, mac2_of. rewrite <- E. rewrite L. reflexivity.
Qed.

Lemma prot3_cookie_msg_join sh pre m2 mp k :
  Zlength m2 = 16 -> Zlength pre = k -> field_compatible (tarray tuchar (k + 16)) [] mp ->
  b2s_bytes sh pre mp * bytes_at sh m2 (offset_val k mp) |-- bytes_at sh (pre ++ m2) mp.
Proof.
  intros L2 Lp FC. pose proof (Zlength_nonneg pre).
  assert (Lt: Zlength (pre ++ m2) = k + 16) by (rewrite Zlength_app; lia).
  rewrite (prot3_cookie_msg_msg2 sh (pre ++ m2) mp); [ | lia | rewrite Lt; auto].
  rewrite Lt. replace (k + 16 - 16) with k by lia.
  rewrite sublist_app1 by lia. rewrite sublist_app2 by lia.
  rewrite <- Lp, sublist_same by lia. replace (Zlength pre - Zlength pre) with 0 by lia.
  replace (Zlength pre + 16 - Zlength pre) with (Zlength m2) by lia. rewrite sublist_same by lia.
  rewrite prot3_cookie_msg_ba, L2. apply derives_refl.
Qed.

Lemma prot3_cookie_msg_cfold shp p (Ck: cookie) m1 lk :
  cookie_ok Ck -> Zlength m1 = 16 -> @field_compatible Cookie.CS t_peer [] p ->
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._birthdate) (Vlong (ck_birth Ck)) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._is_valid) (Val.of_bool (ck_valid Ck)) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._cookie) (bytes (ck_cookie Ck)) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._have_sent_mac1) (Vint Int.one) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) (bytes m1) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._cookie_decryption_key) (bytes (ck_dkey Ck)) p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._message_mac1_key) (bytes (ck_mkey Ck)) p *
  spacer shp 466 468 p *
  @field_at Cookie.CS shp t_peer (DOT C._latest_cookie DOT C._lock) lk p
  |-- cookie_rep shp (cookie_addr p) (mkCookie (ck_birth Ck) (ck_valid Ck) (ck_cookie Ck) true m1 (ck_dkey Ck) (ck_mkey Ck)).
Proof.
  intros Hok L FC. unfold cookie_rep. Exists lk.
  rewrite (prot3_cookie_msg_cookie_eq shp p _ lk FC).
  unfold_field_at 9%nat. unfold cookie_val; cbn [fst snd ck_birth ck_valid ck_cookie ck_sent ck_last_mac1 ck_dkey ck_mkey].
  destruct Hok as (? & ? & ? & ?).
  entailer!. unfold cookie_ok; simpl; auto.
Qed.

Lemma prot3_cookie_msg_body_add_mac :
  @semax_body (QPvarspecs Cookie.qp) prot3_cookie_msg_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_add_mac_to_packet wg_cookie_add_mac_to_packet_spec.
Proof.
start_function.
unfold cookie_rep. Intros lk.
rewrite (prot3_cookie_msg_cookie_eq shp p Ck lk (prot3_cookie_msg_fc_peer p H)).
assert_PROP (field_compatible (tarray tuchar (Zlength msg)) [] mp) as FCm
  by (rewrite prot3_cookie_msg_ba; entailer!).
forward.
match goal with |- context [temp C._macs ?v] => assert (Hm: v = offset_val (Zlength msg - 32) mp) end.
{ pose proof (field_compatible_isptr _ _ _ FCm) as Hp. destruct mp; try contradiction. simpl.
  f_equal. rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  replace (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 32))) with (Ptrofs.repr 32) by reflexivity.
  unfold Ptrofs.of_int64. rewrite Int64.unsigned_repr by rep_lia.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr. f_equal; f_equal; lia. }
rewrite Hm. clear Hm.
assert_PROP (field_compatible (Tstruct C._wg_peer noattr) (DOT C._latest_cookie) p) as FCc by entailer!.
unfold_field_at 1%nat.
unfold cookie_val; cbn [fst snd].
destruct H1 as (Lck & Llm & Ldk & Lmk).
rewrite (prot3_cookie_msg_fa_mkey shp (ck_mkey Ck) p Lmk).
rewrite (prot3_cookie_msg_msg3 shm msg mp) by (first [lia | auto]).
sep_apply (@data_at_data_at_ Cookie.CS shm (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 32) (Zlength msg - 16) msg)) (offset_val (Zlength msg - 32) mp)).
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ shm (tarray tuchar 16)) by reflexivity.
forward_call (gv, shm, offset_val (Zlength msg - 32) mp, shm, mp, sublist 0 (Zlength msg - 32) msg, shp,
              field_address t_peer (DOT C._latest_cookie DOT C._message_mac1_key) p, ck_mkey Ck).
{ entailer!. simpl. rewrite field_address_offset by auto with field_compatible. simpl.
  rewrite Zlength_sublist by lia. replace (Zlength msg - 32 - 0 + 32) with (Zlength msg) by lia.
  rewrite !offset_offset_val. replace (Zlength msg - 32 + 0) with (Zlength msg - 32) by lia. reflexivity. }
{ rewrite Zlength_sublist by lia. lia. }
remember (MAC (ck_mkey Ck) (sublist 0 (Zlength msg - 32) msg)) as m1 eqn:Em1.
assert (Hm1: Zlength m1 = 16) by (subst m1; unfold MAC; apply prot3_cookie_msg_blake2s_len; lia).
change (prot3_cookie_msg_eq m1 (MAC (ck_mkey Ck) (sublist 0 (Zlength msg - 32) msg))) in Em1.
rewrite (prot3_cookie_msg_ba shm m1). rewrite Hm1.
rewrite (prot3_cookie_msg_fa_last shp (ck_last_mac1 Ck) p Llm).
sep_apply (@data_at_data_at_ Cookie.CS shp (tarray tuchar 16) (bytes (ck_last_mac1 Ck))
             (field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p)).
forward_call (shp, shm, field_address t_peer (DOT C._latest_cookie DOT C._last_mac1_sent) p,
              offset_val (Zlength msg - 32) mp, 16, m1).
forward.
forward.
{ entailer!. destruct (ck_valid Ck); simpl; auto. }
set (c := andb (ck_valid Ck) (negb (birthdate_expired (ck_birth Ck) (Int64.repr 115) (s_boot S)))).
match goal with |- semax _ (PROPx ?Pr (LOCALx ?L (SEPx ?R))) _ _ =>
  forward_if (PROPx Pr (LOCALx (temp C._t'1 (Val.of_bool c) :: L) (SEPx R))) end.
{ forward.
  forward_call (gv, S, ck_birth Ck, Int64.repr 115).
  forward.
  entailer!.
  unfold c. destruct (ck_valid Ck); [| unfold typed_true in H1; simpl in H1; discriminate].
  destruct (birthdate_expired (ck_birth Ck) (Int64.repr 115) (s_boot S)); reflexivity. }
{ forward.
  entailer!.
  unfold c. destruct (ck_valid Ck); [unfold typed_false in H1; simpl in H1; discriminate | reflexivity]. }
pose (msg1 := sublist 0 (Zlength msg - 32) msg ++ m1 ++ sublist (Zlength msg - 16) (Zlength msg) msg).
destruct (prot3_cookie_msg_msg1 msg m1 ltac:(lia) Hm1) as (L1 & S1 & S2 & S3); fold msg1 in L1, S1, S2, S3.
assert (FOLD: b2s_bytes shm (sublist 0 (Zlength msg - 32) msg) mp *
   @data_at Cookie.CS shm (tarray tuchar 16) (map Vubyte m1) (offset_val (Zlength msg - 32) mp) *
   @data_at Cookie.CS shm (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg))
     (offset_val (Zlength msg - 16) mp) |-- bytes_at shm msg1 mp).
{ pose proof (prot3_cookie_msg_msg3_fold shm msg1 mp) as F. rewrite L1, S1, S2, S3 in F.
  apply F; [lia | auto]. }
sep_apply FOLD. clear FOLD.
rewrite (prot3_cookie_msg_msg2 shm msg1 mp) by (rewrite L1; first [lia | auto]).
rewrite L1.
sep_apply (@data_at_data_at_ Cookie.CS shm (tarray tuchar 16) (map Vubyte (sublist (Zlength msg - 16) (Zlength msg) msg1)) (offset_val (Zlength msg - 16) mp)).
assert (Ec: c = andb (ck_valid Ck) (negb (birthdate_expired (ck_birth Ck) (Int64.repr 115) (s_boot S)))) by reflexivity.
clearbody c.
destruct c.
{ forward_if.
  2:{ exfalso; prot3_cookie_msg_contra. }
  rewrite (prot3_cookie_msg_fa_cookie shp (ck_cookie Ck) p Lck).
  rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ shm (tarray tuchar 16)) by reflexivity.
  forward_call (gv, shm, offset_val (Zlength msg - 16) mp, shm, mp, sublist 0 (Zlength msg - 16) msg1, shp,
                field_address t_peer (DOT C._latest_cookie DOT C._cookie) p, ck_cookie Ck).
  { entailer!. simpl. rewrite field_address_offset by auto with field_compatible. simpl.
    rewrite Zlength_sublist by (rewrite ?L1; lia). replace (Zlength msg - 16 - 0 + 16) with (Zlength msg) by lia.
    rewrite !offset_offset_val. replace (Zlength msg - 32 + 16) with (Zlength msg - 16) by lia. reflexivity. }
  { rewrite Zlength_sublist by (rewrite ?L1; lia). lia. }
  remember (MAC (ck_cookie Ck) (sublist 0 (Zlength msg - 16) msg1)) as m2 eqn:Em2.
  assert (Hm2: Zlength m2 = 16) by (subst m2; unfold MAC; apply prot3_cookie_msg_blake2s_len; lia).
  change (prot3_cookie_msg_eq m2 (MAC (ck_cookie Ck) (sublist 0 (Zlength msg - 16) msg1))) in Em2.
  sep_apply (prot3_cookie_msg_join shm (sublist 0 (Zlength msg - 16) msg1) m2 mp (Zlength msg - 16) Hm2
               ltac:(rewrite Zlength_sublist by (rewrite ?L1; lia); lia)
               ltac:(replace (Zlength msg - 16 + 16) with (Zlength msg) by lia; auto)).
  rewrite <- (prot3_cookie_msg_fa_cookie shp (ck_cookie Ck) p Lck).
  rewrite <- (prot3_cookie_msg_fa_mkey shp (ck_mkey Ck) p Lmk).
  change (@data_at Cookie.CS shp (tarray tuchar 16) (map Vubyte m1)) with (@data_at Cookie.CS shp (tarray tuchar 16) (bytes m1)).
  rewrite <- (prot3_cookie_msg_fa_last shp m1 p Hm1).
  sep_apply (prot3_cookie_msg_cfold shp p Ck m1 lk ltac:(split; auto) Hm1 (prot3_cookie_msg_fc_peer p H)).
  unfold prot3_cookie_msg_eq in Em1, Em2.
  rewrite (prot3_cookie_msg_model Ck msg (s_boot S) m1 Em1 L1). rewrite <- Ec.
  fold msg1. rewrite <- Em2. simpl fst; simpl snd.
  entailer!. }
{ forward_if.
  { exfalso; prot3_cookie_msg_contra. }
  forward_call (shm, offset_val (Zlength msg - 16) mp, 0, 16).
  { entailer!. simpl. rewrite !offset_offset_val. replace (Zlength msg - 32 + 16) with (Zlength msg - 16) by lia. reflexivity. }
  change (Zrepeat (Vubyte (Byte.repr 0)) 16) with (map Vubyte (zeros 16)).
  replace (@data_at Cookie.CS shm (tarray tuchar 16) (map Vubyte (zeros 16)) (offset_val (Zlength msg - 16) mp))
    with (bytes_at shm (zeros 16) (offset_val (Zlength msg - 16) mp)) by (rewrite prot3_cookie_msg_ba; reflexivity).
  sep_apply (prot3_cookie_msg_join shm (sublist 0 (Zlength msg - 16) msg1) (zeros 16) mp (Zlength msg - 16)
               ltac:(reflexivity)
               ltac:(rewrite Zlength_sublist by (rewrite ?L1; lia); lia)
               ltac:(replace (Zlength msg - 16 + 16) with (Zlength msg) by lia; auto)).
  rewrite <- (prot3_cookie_msg_fa_mkey shp (ck_mkey Ck) p Lmk).
  change (@data_at Cookie.CS shp (tarray tuchar 16) (map Vubyte m1)) with (@data_at Cookie.CS shp (tarray tuchar 16) (bytes m1)).
  rewrite <- (prot3_cookie_msg_fa_last shp m1 p Hm1).
  sep_apply (prot3_cookie_msg_cfold shp p Ck m1 lk ltac:(split; auto) Hm1 (prot3_cookie_msg_fc_peer p H)).
  unfold prot3_cookie_msg_eq in Em1.
  rewrite (prot3_cookie_msg_model Ck msg (s_boot S) m1 Em1 L1). rewrite <- Ec.
  fold msg1. cbv beta iota. simpl fst; simpl snd.
  entailer!. }
Qed.

(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)

Lemma prot3_cookie_msg_create_split sh dp (v1 v2: val) (l1 l2: list val) :
  field_compatible t_cmsg [] dp ->
  @data_at Cookie.CS sh t_cmsg ((v1, (v2, (l1, l2))) : reptype t_cmsg) dp =
  (field_at sh t_cmsg (DOT C._header DOT C._type) v1 dp *
  field_at sh t_cmsg (DOT C._receiver_index) v2 dp *
  data_at sh (tarray tuchar 24) l1 (field_address t_cmsg (DOT C._nonce) dp) *
  data_at sh (tarray tuchar 32) l2 (field_address t_cmsg (DOT C._encrypted_cookie) dp))%logic.
Proof.
  intros FC.
  unfold_data_at (data_at sh t_cmsg _ dp).
  unfold_field_at 1%nat.
  rewrite (field_at_data_at sh t_cmsg (DOT C._nonce)).
  rewrite (field_at_data_at sh t_cmsg (DOT C._encrypted_cookie)).
  rewrite !sepcon_assoc. reflexivity.
Qed.

Lemma prot3_cookie_msg_create_undef sh dp :
  @data_at_ Cookie.CS sh t_cmsg dp =
  @data_at Cookie.CS sh t_cmsg ((Vundef, (Vundef, (Zrepeat Vundef 24, Zrepeat Vundef 32))) : reptype t_cmsg) dp.
Proof. reflexivity. Qed.

Lemma prot3_cookie_msg_create_cc_ekey sh c CC :
  checker_rep sh c CC |--
  (@data_at Cookie.CS sh (tarray tuchar 32) (map Vubyte (cc_ekey CC))
     (field_address t_cc (DOT C._cookie_encryption_key) c) *
   (@data_at Cookie.CS sh (tarray tuchar 32) (map Vubyte (cc_ekey CC))
     (field_address t_cc (DOT C._cookie_encryption_key) c) -* checker_rep sh c CC))%logic.
Proof.
  unfold checker_rep at 1. Intros lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at sh t_cc _ c).
  rewrite (field_at_data_at sh t_cc (DOT C._cookie_encryption_key)).
  change (nested_field_type t_cc (DOT C._cookie_encryption_key)) with (tarray tuchar 32).
  unfold bytes at 2.
  cancel.
  apply -> wand_sepcon_adjoint.
  unfold checker_rep. Exists lk.
  erewrite (@data_at_change_composite Noise.CS Cookie.CS _ sh t_cc); [| apply JMeq_refl | prove_cs_preserve_type].
  unfold_data_at (data_at sh t_cc _ c).
  rewrite (field_at_data_at sh t_cc (DOT C._cookie_encryption_key)).
  change (nested_field_type t_cc (DOT C._cookie_encryption_key)) with (tarray tuchar 32).
  unfold bytes at 2.
  entailer!.
Qed.

Lemma prot3_cookie_msg_create_zp gv : @zero_page Noise.CS gv = @zero_page Cookie.CS gv.
Proof. unfold zero_page. apply data_at_cs_eq; [apply JMeq_refl | reflexivity]. Qed.

Lemma prot3_cookie_msg_create_ekey CC now r : cc_ekey (checker_rotate CC now r) = cc_ekey CC.
Proof. unfold checker_rotate. destruct (birthdate_expired _ _ _); reflexivity. Qed.

Lemma prot3_cookie_msg_create_ba16 sh (l: list byte) p :
  Zlength l = 16 -> bytes_at sh l p = @data_at Cookie.CS sh (tarray tuchar 16) (map Vubyte l) p.
Proof. intros H. rewrite prot3_cookie_msg_ba, H. reflexivity. Qed.

Lemma prot3_cookie_msg_create_pb sh (l: list byte) p n :
  Zlength l = n -> n <> 0 -> @data_at Cookie.CS sh (tarray tuchar n) (map Vubyte l) p = @prim_bytes Cookie.CS sh l p.
Proof. intros H Hn. subst n. unfold prim_bytes. rewrite if_false by auto. reflexivity. Qed.

Lemma prot3_cookie_msg_create_mc CC s index nonce msg S r :
  mc_res xaead_enc CC s index nonce msg S r =
  (mkCM (Int.repr 3) index nonce
     (xaead_enc (cc_ekey CC) nonce (sublist (Zlength msg - 32) (Zlength msg - 16) msg)
        (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s)),
   checker_rotate CC (s_boot S) r).
Proof. reflexivity. Qed.

Lemma prot3_cookie_msg_create_ba24 sh (l: list byte) p :
  Zlength l = 24 -> bytes_at sh l p = @data_at Cookie.CS sh (tarray tuchar 24) (map Vubyte l) p.
Proof. intros H. rewrite prot3_cookie_msg_ba, H. reflexivity. Qed.

Lemma prot3_cookie_msg_body_create :
  @semax_body (QPvarspecs Cookie.qp) prot3_cookie_msg_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_create (wg_cookie_message_create_spec xaead_enc).
Proof.
start_function.
unfold skb_rep. Intros.
assert_PROP (field_compatible (tarray tuchar (Zlength msg)) [] (sk_data s)) as FCm
  by (rewrite prot3_cookie_msg_ba; entailer!).
assert_PROP (cc_ok CC /\ field_compatible t_cc [] c) as HccF
  by (sep_apply (prot3_cookie_msg_cc_lf shc c CC); entailer!).
destruct HccF as [Hcc FCc].
assert_PROP (field_compatible t_cmsg [] dp) as FCd by entailer!.
unfold skb_val. forward. forward. forward.
{ entailer!. apply field_compatible_isptr in FCm. destruct (sk_data s); try contradiction; simpl; auto. }
match goal with |- context [temp C._macs ?v] => assert (Hm: v = offset_val (Zlength msg - 32) (sk_data s)) end.
{ pose proof (field_compatible_isptr _ _ _ FCm) as Hp. destruct (sk_data s); try contradiction. simpl.
  f_equal.
  rewrite !(Ptrofs.mul_commut (Ptrofs.repr 1)), !Ptrofs.mul_one.
  replace (Ptrofs.of_int64 (Ptrofs.to_int64 (Ptrofs.repr 32))) with (Ptrofs.repr 32) by reflexivity.
  unfold Ptrofs.of_intu, Ptrofs.of_int. rewrite <- H0.
  rewrite Ptrofs.sub_add_opp, Ptrofs.add_assoc, Ptrofs.neg_repr, ptrofs_add_repr. f_equal; f_equal; lia. }
rewrite Hm. clear Hm.
rewrite prot3_cookie_msg_create_undef, (prot3_cookie_msg_create_split shd dp) by auto.
Intros.
forward. forward.
change (@data_at Cookie.CS shd (tarray tuchar 24) (Zrepeat Vundef 24) (field_address t_cmsg (DOT C._nonce) dp))
  with (@data_at_ Cookie.CS shd (tarray tuchar 24) (field_address t_cmsg (DOT C._nonce) dp)).
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ shd (tarray tuchar 24) (field_address t_cmsg (DOT C._nonce) dp))
  by reflexivity.
forward_call (gv, S, shd, field_address t_cmsg (DOT C._nonce) dp, 24).
Intros nonce.
sep_apply (prot3_cookie_msg_skb_intro shs sp s H1).
rewrite (@data_at__cs_eq Cookie.CS Noise.CS _ Tsh (tarray tuchar 16) v_cookie__1) by reflexivity.
forward_call (gv, shim_draw S nonce, Tsh, v_cookie__1, shs, sp, s, shc, c, CC).
Intros r.
change (s_boot (shim_draw S nonce)) with (s_boot S).
remember (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s) as ck eqn:Eck.
assert (Hck: Zlength ck = 16) by (subst ck; unfold cookie_of, MAC; apply prot3_cookie_msg_blake2s_len; lia).
change (prot3_cookie_msg_eq ck (cookie_of (cc_secret (checker_rotate CC (s_boot S) r)) s)) in Eck.
remember (checker_rotate CC (s_boot S) r) as CC1 eqn:ECC1.
change (prot3_cookie_msg_eq CC1 (checker_rotate CC (s_boot S) r)) in ECC1.
remember (if checker_rotates CC (s_boot S) then shim_draw (shim_draw S nonce) r else shim_draw S nonce)
  as S2 eqn:ES2.
change (prot3_cookie_msg_eq S2 (if checker_rotates CC (s_boot S) then shim_draw (shim_draw S nonce) r
                                else shim_draw S nonce)) in ES2.
assert_PROP (cc_ok CC1) as Hcc1 by (sep_apply (prot3_cookie_msg_cc_lf shc c CC1); entailer!).
sep_apply (prot3_cookie_msg_create_cc_ekey shc c CC1).
rewrite (prot3_cookie_msg_msg3 shm msg (sk_data s)) by auto.
rewrite (prot3_cookie_msg_create_ba16 Tsh ck v_cookie__1 Hck).
rewrite (prot3_cookie_msg_create_ba24 shd nonce _ H2).
rewrite (prot3_cookie_msg_create_pb Tsh ck v_cookie__1 16 Hck) by lia.
rewrite (prot3_cookie_msg_create_pb shm (sublist (Zlength msg - 32) (Zlength msg - 16) msg) _ 16)
  by (try rewrite Zlength_sublist; lia).
assert (Eenc: @data_at Cookie.CS shd (tarray tuchar 32) (Zrepeat Vundef 32)
                (field_address t_cmsg (DOT C._encrypted_cookie) dp) =
              @data_at_ Cookie.CS shd (tarray tuchar (Zlength ck + 16))
                (field_address t_cmsg (DOT C._encrypted_cookie) dp)) by (rewrite Hck; reflexivity).
rewrite Eenc. clear Eenc.
unfold wg_consts. Intros. rewrite prot3_cookie_msg_create_zp.
assert (Hek: Zlength (cc_ekey CC1) = 32) by (destruct Hcc1 as (_ & Hk & _); exact Hk).
forward_call (shd, field_address t_cmsg (DOT C._encrypted_cookie) dp, Tsh, v_cookie__1, ck,
              shm, offset_val (Zlength msg - 32) (sk_data s), sublist (Zlength msg - 32) (Zlength msg - 16) msg,
              shd, field_address t_cmsg (DOT C._nonce) dp, nonce,
              shc, field_address t_cc (DOT C._cookie_encryption_key) c, cc_ekey CC1, gv).
{ entailer!. rewrite Hck, Zlength_sublist by lia. replace (Zlength msg - 16 - (Zlength msg - 32)) with 16 by lia.
  simpl. rewrite !field_address_offset by auto with field_compatible. simpl.
  rewrite isptr_offset_val_zero by auto. reflexivity. }
{ rewrite Zlength_sublist by lia. rep_lia. }
remember (xaead_enc (cc_ekey CC1) nonce (sublist (Zlength msg - 32) (Zlength msg - 16) msg) ck) as X eqn:EXa.
assert_PROP (Zlength X = 32) as HX.
{ entailer!. rewrite Zlength_map in *. lia. }
sep_apply (modus_ponens_wand
  (@data_at Cookie.CS shc (tarray tuchar 32) (map Vubyte (cc_ekey CC1))
     (field_address t_cc (DOT C._cookie_encryption_key) c)) (checker_rep shc c CC1)).
rewrite <- (prot3_cookie_msg_create_pb Tsh ck v_cookie__1 16 Hck) by lia.
rewrite <- (prot3_cookie_msg_create_pb shm (sublist (Zlength msg - 32) (Zlength msg - 16) msg) _ 16)
  by (try rewrite Zlength_sublist; lia).
sep_apply (prot3_cookie_msg_msg3_fold shm msg (sk_data s) H FCm).
sep_apply (data_at_data_at_ Tsh (tarray tuchar 16) (map Vubyte ck) v_cookie__1).
rewrite Hck. simpl (16 + 16).
Exists nonce r.
rewrite prot3_cookie_msg_create_mc.
unfold prot3_cookie_msg_eq in ECC1, Eck, ES2.
rewrite <- ECC1, <- Eck, <- ES2.
assert (Ek: cc_ekey CC1 = cc_ekey CC) by (rewrite ECC1; apply prot3_cookie_msg_create_ekey).
rewrite <- Ek, <- EXa.
clear Eck ES2 EXa.
cbn [fst snd].
unfold cmsg_rep, cmsg_val. cbn [cm_type cm_receiver cm_nonce cm_enc].
rewrite (prot3_cookie_msg_create_split shd dp) by auto.
unfold wg_consts. rewrite <- prot3_cookie_msg_create_zp.
unfold bytes.
rewrite prop_true_andp by (split; auto).
entailer!.
Qed.

(* ---------------------------------------------------------------------------------------------- *)

(* ---------------------------------------------------------------------------------------------- *)

(* the body is proved in prot3_cookie_msg_consume.v; it needs xaead_props (decrypt's plaintext length: the
   local u8 cookie[16] and cookie_ok of the new cookie), agreed with *)
Require WgNoise.proof.protocol.prot3_cookie_msg_consume.
Context (prot3_cookie_msg_HXA: xaead_props xaead_enc xaead_dec).

Lemma prot3_cookie_msg_body_consume :
  @semax_body (QPvarspecs Cookie.qp) prot3_cookie_msg_G Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_consume (wg_cookie_message_consume_spec xaead_dec).
Proof.
  exact (WgNoise.proof.protocol.prot3_cookie_msg_consume.prot3_cmc_body
           x25519 aead_enc aead_dec xaead_enc xaead_dec CSw prot3_cookie_msg_HXA).
Qed.

(* ---------------------------------------------------------------------------------------------- *)

End CookieMsg.

Theorem prot_bodies3_cookie_msg :
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (CSw: compspecs),
  x25519_props x25519 -> aead_props aead_enc aead_dec -> xaead_props xaead_enc xaead_dec ->
  (@semax_body (QPvarspecs Cookie.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_add_mac_to_packet wg_cookie_add_mac_to_packet_spec) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_create (wg_cookie_message_create_spec xaead_enc)) /\
  (@semax_body (QPvarspecs Cookie.qp) (Gprot3 x25519 aead_enc aead_dec xaead_enc xaead_dec CSw Cookie.CS) Cookie.CS
      WgNoise.cookie.code.f_wg_cookie_message_consume (wg_cookie_message_consume_spec xaead_dec)).
Proof.
  intros. split; [| split].
  - apply prot3_cookie_msg_body_add_mac.
  - apply prot3_cookie_msg_body_create.
  - apply prot3_cookie_msg_body_consume; auto.
Qed.
