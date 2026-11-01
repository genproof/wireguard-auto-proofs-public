(* (the series P22/P23 replaced the helpers chacha20_crypt_long / poly1305_update_long by
   direct calls of chacha20_crypt / poly1305_update with the size_t lengths): body proof of __chacha20poly1305_encrypt (size_t lengths), against aead_spec3.aead_G3. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require WgNoise.chacha.code WgNoise.chacha_block.code WgNoise.poly1305.code WgNoise.poly1305_donna32.code
        WgNoise.chacha20poly1305.code WgNoise.shim.code.
Require Import WgNoise.proof.libc.spec.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.common.wg3_iface.
Require Import WgNoise.proof.aead.aead_spec3.
Require Import WgNoise.proof.aead.aead_cce.
Require Import WgNoise.proof.aead.aead_bytes.
Require Import WgNoise.proof.protocol.prot_dec3.
Require Import WgNoise.proof.aead.aead_out3.

Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* model facts                                                             *)
(* ---------------------------------------------------------------------- *)

Lemma enc3_Zlength_words_bytes ws : Zlength (words_bytes ws) = 4 * Zlength ws.
Proof.
  unfold words_bytes. induction ws; cbn [map concat]; auto.
  rewrite Zlength_app, IHws, Zlength_cons. unfold le32_bytes. rewrite !Zlength_cons, Zlength_nil. lia.
Qed.

Lemma enc3_Zlength_qround x a b c d : Zlength (chacha_qround x a b c d) = Zlength x.
Proof. unfold chacha_qround. rewrite !Zlength_upd_Znth. reflexivity. Qed.

Lemma enc3_Zlength_dround x : Zlength (chacha_dround x) = Zlength x.
Proof. unfold chacha_dround. rewrite !enc3_Zlength_qround. reflexivity. Qed.

(* never let the kernel compare chacha_rounds (S n) x with chacha_rounds n (chacha_dround x) *)
Lemma enc3_Zlength_rounds n x : Zlength (chacha_rounds n x) = Zlength x.
Proof.
  revert x; induction n; intros x; [reflexivity |].
  change (Zlength ((fix rounds (n : nat) (x : list int) {struct n} : list int :=
                      match n with O => x | S k => rounds k (chacha_dround x) end) n (chacha_dround x))
          = Zlength x).
  transitivity (Zlength (chacha_dround x)).
  - exact (IHn (chacha_dround x)).
  - apply enc3_Zlength_dround.
Qed.

Lemma enc3_Zlength_add_words a b : Zlength a = Zlength b -> Zlength (add_words a b) = Zlength a.
Proof.
  intros H. unfold add_words. rewrite Zlength_map. rewrite !Zlength_correct in *.
  rewrite combine_length. lia.
Qed.

Lemma enc3_Zlength_block_bytes n st : Zlength st = 16 -> Zlength (chacha_block_bytes n st) = 64.
Proof.
  intros H. unfold chacha_block_bytes, chacha_block_words.
  rewrite enc3_Zlength_words_bytes, enc3_Zlength_add_words; rewrite ?enc3_Zlength_rounds; lia.
Qed.

Lemma enc3_Zlength_advance st k : Zlength (chacha_advance st k) = Zlength st.
Proof. unfold chacha_advance. apply Zlength_upd_Znth. Qed.

Lemma enc3_Zlength_stream n st k :
  Zlength st = 16 -> Zlength (chacha_stream n st k) = 64 * Z.of_nat k.
Proof.
  revert st; induction k; intros st H; cbn [chacha_stream]; auto.
  rewrite Zlength_app, enc3_Zlength_block_bytes, IHk by (rewrite ?enc3_Zlength_advance; auto). lia.
Qed.

Lemma enc3_Zlength_xor a b : Zlength (xor_bytes a b) = Z.min (Zlength a) (Zlength b).
Proof.
  unfold xor_bytes. rewrite Zlength_map, !Zlength_correct, combine_length. lia.
Qed.

Lemma enc3_Zlength_chacha_xor n st m : Zlength st = 16 -> Zlength (chacha_xor n st m) = Zlength m.
Proof.
  intros H. unfold chacha_xor. rewrite enc3_Zlength_xor, enc3_Zlength_stream by auto.
  unfold chacha_nblocks. pose proof (Zlength_nonneg m).
  rewrite Z2Nat.id by (apply Z.div_pos; lia).
  assert (Zlength m <= 64 * ((Zlength m + 63) / 64)).
  { pose proof (Z.mod_pos_bound (Zlength m + 63) 64). pose proof (Z.div_mod (Zlength m + 63) 64). lia. }
  lia.
Qed.

Lemma enc3_xor_zeros k b : Zlength b = k -> xor_bytes (Zrepeat Byte.zero k) b = b.
Proof.
  intros <-. induction b as [| x b IH]; auto.
  rewrite Zlength_cons. unfold Zrepeat. rewrite Z2Nat.inj_succ by (apply Zlength_nonneg). simpl.
  unfold xor_bytes in *. simpl. rewrite Byte.xor_zero_l. f_equal. exact IH.
Qed.

Lemma enc3_xor_app a1 a2 b1 b2 :
  Zlength a1 = Zlength b1 -> xor_bytes (a1 ++ a2) (b1 ++ b2) = xor_bytes a1 b1 ++ xor_bytes a2 b2.
Proof.
  revert b1; induction a1; intros b1 H; destruct b1; simpl; auto;
    rewrite ?Zlength_cons, ?Zlength_nil in H.
  - pose proof (Zlength_nonneg b1); lia.
  - pose proof (Zlength_nonneg a1); lia.
  - unfold xor_bytes in *; simpl. f_equal. apply IHa1. lia.
Qed.

Lemma enc3_xor_zeros_prefix k b : 0 <= k <= Zlength b ->
  xor_bytes (Zrepeat Byte.zero k) b = sublist 0 k b.
Proof.
  intros Hk. rewrite <- (enc3_xor_zeros k (sublist 0 k b)) by (rewrite Zlength_sublist; lia).
  assert (Hb: b = sublist 0 k b ++ sublist k (Zlength b) b)
    by (rewrite sublist_rejoin, sublist_same; auto; lia).
  rewrite Hb at 1. rewrite <- (app_nil_r (Zrepeat Byte.zero k)) at 1. rewrite enc3_xor_app.
  - change (xor_bytes [] (sublist k (Zlength b) b)) with (@nil byte). apply app_nil_r.
  - rewrite Zlength_Zrepeat, Zlength_sublist; lia.
Qed.

(* the one-time key: chacha20_crypt of 32 zero bytes *)
Lemma enc3_otk st : Zlength st = 16 -> chacha_xor 10 st (Zrepeat Byte.zero 32) = aead_otk st.
Proof.
  intros H. unfold chacha_xor, aead_otk. rewrite Zlength_Zrepeat by lia.
  change (Z.to_nat (chacha_nblocks 32)) with 1%nat. cbn [chacha_stream]. rewrite app_nil_r.
  apply enc3_xor_zeros_prefix. rewrite enc3_Zlength_block_bytes by auto. lia.
Qed.

Lemma enc3_Zlength_otk st : Zlength st = 16 -> Zlength (aead_otk st) = 32.
Proof. intros H. unfold aead_otk. rewrite Zlength_sublist; rewrite ?enc3_Zlength_block_bytes; auto; lia. Qed.

Lemma enc3_nblocks_32 : chacha_nblocks (Zlength (Zrepeat Byte.zero 32)) = 1.
Proof. reflexivity. Qed.

Lemma enc3_and15 z : 0 <= z <= Int64.max_unsigned ->
  Int64.and (Int64.repr z) (Int64.repr 15) = Int64.repr (z mod 16).
Proof.
  intros Hz. change (Int64.repr 15) with (Int64.sub (Int64.repr 16) Int64.one).
  rewrite <- (Int64.modu_and _ _ (Int64.repr 4)) by reflexivity.
  unfold Int64.modu. rewrite !Int64.unsigned_repr by (rep_lia || (split; [cbv; congruence | rep_lia])).
  reflexivity.
Qed.

Lemma enc3_pad_len z : 0 <= z <= Int64.max_unsigned ->
  Int64.Z_mod_modulus (16 - Int64.Z_mod_modulus (Z.land (Int64.Z_mod_modulus z) 15)) = 16 - z mod 16.
Proof.
  intros Hz. assert (Hm: Int64.modulus = Int64.max_unsigned + 1) by reflexivity.
  rewrite !Int64.Z_mod_modulus_eq. rewrite (Z.mod_small z) by lia.
  change 15 with (Z.ones 4). rewrite Z.land_ones by lia. change (2 ^ 4) with 16.
  pose proof (Z.mod_pos_bound z 16).
  assert (16 < Int64.modulus) by (rewrite Hm; rep_lia).
  rewrite (Z.mod_small (z mod 16)) by lia. rewrite Z.mod_small by lia. reflexivity.
Qed.

Lemma enc3_Zlength_le64 z : Zlength (le64_bytes z) = 8.
Proof. reflexivity. Qed.

Lemma enc3_lens1 (otk: list byte) za : Zlength otk = 32 ->
  sublist 0 0 (map Vubyte otk) ++ map Vubyte (le64_bytes za) ++ sublist (0 + 8) (Zlength (map Vubyte otk)) (map Vubyte otk)
  = map Vubyte (le64_bytes za ++ sublist 8 32 otk).
Proof.
  intros H. change (0 + 8) with 8. rewrite Zlength_map, H, sublist_nil, app_nil_l, map_app, sublist_map. reflexivity.
Qed.

Lemma enc3_lens2 (otk la lm: list byte) : Zlength otk = 32 -> Zlength la = 8 -> Zlength lm = 8 ->
  sublist 0 8 (map Vubyte (la ++ sublist 8 32 otk)) ++ map Vubyte lm ++
  sublist (8 + 8) (Zlength (map Vubyte (la ++ sublist 8 32 otk))) (map Vubyte (la ++ sublist 8 32 otk))
  = map Vubyte (la ++ lm) ++ map Vubyte (sublist 16 32 otk).
Proof. intros. list_solve. Qed.

Lemma enc3_Zlength_L1 (otk la: list byte) : Zlength otk = 32 -> Zlength la = 8 ->
  Zlength (map Vubyte (la ++ sublist 8 32 otk)) = 32.
Proof. intros. rewrite Zlength_map, Zlength_app, Zlength_sublist; lia. Qed.

Lemma enc3_sub16 (l1 l2: list byte) : Zlength l1 = 16 -> Zlength l2 = 16 ->
  sublist 0 16 (map Vubyte l1 ++ map Vubyte l2) = map Vubyte l1 /\
  sublist 16 32 (map Vubyte l1 ++ map Vubyte l2) = map Vubyte l2.
Proof. intros. split; list_solve. Qed.

Lemma enc3_pad16_nz (x: list byte) : Zlength x mod 16 <> 0 ->
  pad16 x = Zrepeat Byte.zero (16 - Zlength x mod 16).
Proof.
  intros H. unfold pad16. f_equal. pose proof (Z.mod_pos_bound (Zlength x) 16). rewrite Z.mod_small; lia.
Qed.

Lemma enc3_pad16_z (x: list byte) : Zlength x mod 16 = 0 -> pad16 x = [].
Proof. intros H. unfold pad16. rewrite H. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* separation-logic facts                                                  *)
(* ---------------------------------------------------------------------- *)

Lemma enc3_wand_split (P Q R: mpred) : P = (Q * R)%logic -> P |-- Q * (Q -* P).
Proof.
  intros ->. cancel. apply wand_sepcon_adjoint. cancel.
Qed.

Lemma enc3_split2 {cs: compspecs} sh n i (v: list val) p :
  0 <= i <= n -> Zlength v = n -> field_compatible (tarray tuchar n) [] p ->
  data_at sh (tarray tuchar n) v p =
  (data_at sh (tarray tuchar i) (sublist 0 i v) p *
   data_at sh (tarray tuchar (n - i)) (sublist i n v) (offset_val i p))%logic.
Proof.
  intros. unfold tarray. rewrite (split2_data_at_Tarray_tuchar sh n i) by lia.
  fold (tarray tuchar n). rewrite arr_field_address0 by (auto; lia).
  change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity.
Qed.

Lemma enc3_split2_ {cs: compspecs} sh n i p :
  0 <= i <= n -> field_compatible (tarray tuchar n) [] p ->
  data_at_ sh (tarray tuchar n) p =
  (data_at_ sh (tarray tuchar i) p * data_at_ sh (tarray tuchar (n - i)) (offset_val i p))%logic.
Proof.
  intros. rewrite !data_at__tarray. rewrite (enc3_split2 sh n i) by (auto; rewrite Zlength_Zrepeat; lia).
  rewrite !sublist_Zrepeat by lia. f_equal; f_equal; f_equal; lia.
Qed.

(* a prefix of the zero page as an input buffer *)
Lemma enc3_zero_page_prefix {cs: compspecs} gv k : 0 <= k <= 64 ->
  zero_page gv |-- prim_bytes Ers (Zrepeat Byte.zero k) (gv _quickproof_zero_page) *
    (prim_bytes Ers (Zrepeat Byte.zero k) (gv _quickproof_zero_page) -* zero_page gv).
Proof.
  intros Hk. unfold zero_page. assert_PROP (field_compatible (tarray tuchar 64) [] (gv _quickproof_zero_page))
    by entailer!.
  unfold prim_bytes. rewrite Zlength_Zrepeat by lia. if_tac.
  - apply (enc3_wand_split _ emp (data_at Ers (tarray tuchar 64) (Zrepeat (Vubyte Byte.zero) 64) (gv _quickproof_zero_page))).
    rewrite emp_sepcon. reflexivity.
  - apply enc3_wand_split with
      (R := data_at Ers (tarray tuchar (64 - k)) (Zrepeat (Vubyte Byte.zero) (64 - k)) (offset_val k (gv _quickproof_zero_page))).
    rewrite (enc3_split2 Ers 64 k) by (auto; try rewrite Zlength_Zrepeat; lia).
    rewrite !sublist_Zrepeat by lia. rewrite map_Zrepeat. f_equal; f_equal; f_equal; lia.
Qed.

(* an output byte array as an input buffer *)
Lemma enc3_prim_bytes_of {cs: compspecs} sh n (l: list byte) p : Zlength l = n ->
  data_at sh (tarray tuchar n) (map Vubyte l) p |--
  prim_bytes sh l p * (prim_bytes sh l p -* data_at sh (tarray tuchar n) (map Vubyte l) p).
Proof.
  intros <-. unfold prim_bytes. if_tac.
  - apply (enc3_wand_split _ emp (data_at sh (tarray tuchar (Zlength l)) (map Vubyte l) p)).
    rewrite emp_sepcon. reflexivity.
  - apply (enc3_wand_split _ _ emp). rewrite sepcon_emp. reflexivity.
Qed.

Lemma enc3_prim_bytes_fold {cs: compspecs} sh n (l: list byte) p : Zlength l = n -> 0 < n ->
  data_at sh (tarray tuchar n) (map Vubyte l) p = prim_bytes sh l p.
Proof. intros <- Hn. unfold prim_bytes. if_tac; [lia | reflexivity]. Qed.

Lemma enc3_data_at_len {cs: compspecs} sh n (v: list val) p : Zlength v = n ->
  data_at sh (tarray tuchar n) v p = data_at sh (tarray tuchar (Zlength v)) v p.
Proof. intros <-. reflexivity. Qed.

(* compspecs conversions (never let unification compare two compspecs: it unfolds them) *)
Lemma enc3_cpt_ctx :
  @cs_preserve_type Chacha20poly1305.CS Poly1305.CS (@coeq Chacha20poly1305.CS Poly1305.CS _) t_p1305_ctx = true.
Proof. vm_compute. reflexivity. Qed.

Lemma enc3_ctx_to_poly sh p :
  @data_at_ Chacha20poly1305.CS sh t_p1305_ctx p = @data_at_ Poly1305.CS sh t_p1305_ctx p.
Proof.
  pose proof (@data_at__change_composite Chacha20poly1305.CS Poly1305.CS _ sh t_p1305_ctx enc3_cpt_ctx) as E.
  exact (f_equal (fun f => f p) E).
Qed.

Lemma enc3_ctx_from_poly sh v p :
  @data_at Poly1305.CS sh t_p1305_ctx v p |-- @data_at_ Chacha20poly1305.CS sh t_p1305_ctx p.
Proof. rewrite enc3_ctx_to_poly. apply data_at_data_at_. Qed.

Lemma enc3_cpt_state :
  @cs_preserve_type Chacha20poly1305.CS ChachaBlock.CS (@coeq Chacha20poly1305.CS ChachaBlock.CS _) t_chacha_state
  = true.
Proof. vm_compute. reflexivity. Qed.

Lemma enc3_state_to_block sh p :
  @data_at_ Chacha20poly1305.CS sh t_chacha_state p = @data_at_ ChachaBlock.CS sh t_chacha_state p.
Proof.
  pose proof (@data_at__change_composite Chacha20poly1305.CS ChachaBlock.CS _ sh t_chacha_state enc3_cpt_state) as E.
  exact (f_equal (fun f => f p) E).
Qed.

Lemma enc3_off0 {cs: compspecs} sh n (v: list val) p : isptr p ->
  data_at sh (tarray tuchar n) v p = data_at sh (tarray tuchar n) v (offset_val 0 p).
Proof. intros. rewrite isptr_offset_val_zero by auto. reflexivity. Qed.

Lemma enc3_prim_bytes_cs {cs1 cs2: compspecs} sh bs p : @prim_bytes cs1 sh bs p = @prim_bytes cs2 sh bs p.
Proof. unfold prim_bytes. if_tac; auto. apply aead_data_at_tuchar_cs. Qed.

Lemma enc3_b_join {cs: compspecs} sh (l: list byte) (v: list val) p :
  Zlength l = 16 -> Zlength v = 16 -> field_compatible (tarray tuchar 32) [] p ->
  prim_bytes sh l p * data_at sh (tarray tuchar 16) v (offset_val 16 p) |-- data_at_ sh (tarray tuchar 32) p.
Proof.
  intros Hl Hv FC. rewrite <- (enc3_prim_bytes_fold sh 16 l p Hl) by lia.
  rewrite (enc3_split2_ sh 32 16 p) by (auto; lia). change (32 - 16) with 16.
  apply sepcon_derives; apply data_at_data_at_.
Qed.

Lemma enc3_dst_join {cs: compspecs} sh n (l1 l2: list byte) p :
  Zlength l1 = n -> Zlength l2 = 16 -> field_compatible (tarray tuchar (n + 16)) [] p ->
  data_at sh (tarray tuchar n) (map Vubyte l1) p * data_at sh (tarray tuchar 16) (map Vubyte l2) (offset_val n p)
  |-- data_at sh (tarray tuchar (n + 16)) (map Vubyte (l1 ++ l2)) p.
Proof.
  intros H1 H2 FC. pose proof (Zlength_nonneg l1).
  rewrite (enc3_split2 sh (n + 16) n) by (auto; try lia; rewrite Zlength_map, Zlength_app; lia).
  rewrite map_app. rewrite sublist_app1 by (rewrite ?Zlength_map; lia).
  rewrite sublist_app2 by (rewrite ?Zlength_map; lia).
  rewrite !Zlength_map. rewrite sublist_same by (rewrite ?Zlength_map; lia).
  rewrite sublist_same by (rewrite ?Zlength_map; lia). replace (n + 16 - n) with 16 by lia. apply derives_refl.
Qed.

(* an equation hidden from subst (VST's automation substitutes equations; the kernel then computes) *)
Definition enc3_hide (P: Prop) : Prop := P.

(* forward_call runs `change_compspecs` on every call's precondition: between Chacha20poly1305.CS and
   Poly1305.CS it makes the unifier compare the two compspecs (reptype of a converted data_at), which never
   ends.  Disabled here: every cross-unit call gets its arguments converted by the lemmas above. *)
#[local] Ltac change_compspecs' cs cs' ::= fail.
(* forward_call's argument check runs `simpl` on the whole entailment, which never ends on a Poly1305.CS
   data_at_ of the poly1305 context: only the argument equation is simplified here. *)
#[local] Ltac check_vl_eq_args ::=
  first [ solve [ cbv beta; go_lower; apply prop_right; simpl;
                  repeat (match goal with |- _ :: _ = _ :: _ => f_equal end);
                  try reflexivity; try (apply isptr_offset_val_zero; assumption) ]
        | idtac ].

(* forward_call's my_auto proves `readable_share Tsh` (or a Zlength of a model term) by computation, which the
   kernel then redoes at Qed (stack overflow): the share facts by lemma, the rest from the hypotheses. *)
#[local] Ltac prove_PROP_preconditions ::=
  unfold fold_right_and; repeat rewrite and_True;
  repeat match goal with |- _ /\ _ => split end;
  try apply writable_share_top; try apply readable_share_top; try assumption; my_auto.

Section Enc3.
#[local] Existing Instance Chacha20poly1305.CS.

Definition t_b3 : type := Tstruct WgNoise.chacha20poly1305.code.__502 noattr.
Definition b3_block0 (p: val) : val := field_address t_b3 (DOT WgNoise.chacha20poly1305.code._block0) p.

Lemma enc3_b_data_at_ p : field_compatible t_b3 [] p -> data_at_ Tsh t_b3 p = data_at_ Tsh (tarray tuchar 32) p.
Proof.
  intros FC. unfold t_b3. unfold_data_at (data_at_ _ _ p). rewrite field_at_data_at.
  rewrite field_compatible_field_address by (apply field_compatible_cons; split; auto; left; reflexivity).
  simpl. rewrite isptr_offset_val_zero by (destruct FC; auto). reflexivity.
Qed.

(* the callees of other units, restated at Chacha20poly1305.CS (funspec_sub of their specifications) *)
Definition enc3_init_spec :=
  DECLARE _poly1305_init
  WITH sh: share, desc: val, ksh: share, kp: val, key: list byte
  PRE [ tptr t_p1305_ctx, tptr tuchar ]
    PROP (writable_share sh; readable_share ksh; Zlength key = 32)
    PARAMS (desc; kp)
    SEP (data_at_ sh t_p1305_ctx desc; data_at ksh (tarray tuchar 32) (map Vubyte key) kp)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (p1305_state sh key [] desc; data_at ksh (tarray tuchar 32) (map Vubyte key) kp).

Definition enc3_update_spec :=
  DECLARE _poly1305_update
  WITH sh: share, desc: val, key: list byte, msg: list byte, dsh: share, src: val, data: list byte
  PRE [ tptr t_p1305_ctx, tptr tuchar, tulong ]
    PROP (writable_share sh; readable_share dsh; Zlength data <= Int64.max_unsigned)
    PARAMS (desc; src; Vlong (Int64.repr (Zlength data)))
    SEP (p1305_state sh key msg desc; prim_bytes dsh data src)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (p1305_state sh key (msg ++ data) desc; prim_bytes dsh data src).

Definition enc3_final_spec :=
  DECLARE _poly1305_final
  WITH sh: share, desc: val, key: list byte, msg: list byte, osh: share, dst: val
  PRE [ tptr t_p1305_ctx, tptr tuchar ]
    PROP (writable_share sh; writable_share osh)
    PARAMS (desc; dst)
    SEP (p1305_state sh key msg desc; data_at_ osh (tarray tuchar 16) dst)
  POST [ tvoid ]
    PROP () RETURN ()
    SEP (data_at_ sh t_p1305_ctx desc;
         data_at osh (tarray tuchar 16) (map Vubyte (poly1305_tag key msg)) dst).

Definition enc3_zeroize_spec :=
  DECLARE _chacha_zeroize_state
  WITH sh: share, state: val
  PRE [ tptr t_chacha_state ]
    PROP (writable_share sh) PARAMS (state) SEP (data_at_ sh t_chacha_state state)
  POST [ tvoid ]
    PROP () RETURN () SEP (data_at_ sh t_chacha_state state).

Lemma enc3_pre_mono P Q G R R' gargs :
  fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx P (PARAMSx Q (GLOBALSx G (SEPx R))) gargs |-- PROPx P (PARAMSx Q (GLOBALSx G (SEPx R'))) gargs.
Proof.
  intros HR. unfold PROPx, PARAMSx, GLOBALSx, SEPx, LOCALx, argsassert2assert. simpl.
  apply andp_derives; [apply derives_refl |]. apply andp_derives; [apply derives_refl |].
  apply andp_derives; [apply derives_refl |]. exact HR.
Qed.

Lemma enc3_post_mono P Q R R' rho :
  fold_right_sepcon R |-- fold_right_sepcon R' ->
  PROPx P (LOCALx Q (SEPx R)) rho |-- PROPx P (LOCALx Q (SEPx R')) rho.
Proof.
  intros HR. unfold PROPx, LOCALx, SEPx. simpl.
  apply andp_derives; [apply derives_refl |]. apply andp_derives; [apply derives_refl |]. exact HR.
Qed.

Lemma enc3_init_sub : funspec_sub (snd poly1305_init_spec) (snd enc3_init_spec).
Proof.
  apply NDsubsume_subsume; [split; extensionality gv; reflexivity |].
  split; [split; reflexivity |]. intros w; simpl in w; intros [g args].
  destruct w as [[[[sh desc] ksh] kp] key].
  Exists (sh, desc, ksh, kp, key) (emp: mpred). cbv beta iota zeta. rewrite emp_sepcon. apply andp_right.
  - apply andp_left2. apply enc3_pre_mono. cbn [fold_right_sepcon].
    apply sepcon_derives; [exact (derives_refl' _ _ (enc3_ctx_to_poly sh desc)) |].
    apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@aead_data_at_tuchar_cs Chacha20poly1305.CS Poly1305.CS ksh 32 _ kp)).
  - apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply enc3_post_mono.
    cbn [fold_right_sepcon]. apply sepcon_derives; [apply derives_refl |].
    apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@aead_data_at_tuchar_cs Poly1305.CS Chacha20poly1305.CS ksh 32 _ kp)).
Qed.

Lemma enc3_update_sub : funspec_sub (snd poly1305_update_spec3) (snd enc3_update_spec).
Proof.
  apply NDsubsume_subsume; [split; extensionality gv; reflexivity |].
  split; [split; reflexivity |]. intros w; simpl in w; intros [g args].
  destruct w as [[[[[[sh desc] key] msg] dsh] src] data].
  Exists (sh, desc, key, msg, dsh, src, data) (emp: mpred). cbv beta iota zeta. rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2. apply enc3_pre_mono. cbn [fold_right_sepcon].
    apply sepcon_derives; [apply derives_refl |]. apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@enc3_prim_bytes_cs Chacha20poly1305.CS Poly1305.CS dsh data src)).
  - apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply enc3_post_mono.
    cbn [fold_right_sepcon]. apply sepcon_derives; [apply derives_refl |].
    apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@enc3_prim_bytes_cs Poly1305.CS Chacha20poly1305.CS dsh data src)).
Qed.

Lemma enc3_final_sub : funspec_sub (snd poly1305_final_spec) (snd enc3_final_spec).
Proof.
  apply NDsubsume_subsume; [split; extensionality gv; reflexivity |].
  split; [split; reflexivity |]. intros w; simpl in w; intros [g args].
  destruct w as [[[[[sh desc] key] msg] osh] dst].
  Exists (sh, desc, key, msg, osh, dst) (emp: mpred). cbv beta iota zeta. rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2. apply enc3_pre_mono. cbn [fold_right_sepcon].
    apply sepcon_derives; [apply derives_refl |]. apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@aead_data_at__tuchar_cs Chacha20poly1305.CS Poly1305.CS osh 16 dst)).
  - apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply enc3_post_mono.
    cbn [fold_right_sepcon]. apply sepcon_derives; [apply enc3_ctx_from_poly |].
    apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (@aead_data_at_tuchar_cs Poly1305.CS Chacha20poly1305.CS osh 16 _ dst)).
Qed.

Lemma enc3_zeroize_sub : funspec_sub (snd chacha_zeroize_state_spec) (snd enc3_zeroize_spec).
Proof.
  apply NDsubsume_subsume; [split; extensionality gv; reflexivity |].
  split; [split; reflexivity |]. intros w; simpl in w; intros [g args].
  destruct w as [sh state].
  Exists (sh, state) (emp: mpred). cbv beta iota zeta. rewrite emp_sepcon.
  apply andp_right.
  - apply andp_left2. apply enc3_pre_mono. cbn [fold_right_sepcon].
    apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (enc3_state_to_block sh state)).
  - apply prop_right. intros rho'. rewrite emp_sepcon. apply andp_left2. apply enc3_post_mono.
    cbn [fold_right_sepcon]. apply sepcon_derives; [| apply derives_refl].
    exact (derives_refl' _ _ (eq_sym (enc3_state_to_block sh state))).
Qed.

Theorem aead_encrypt_bodies3 :
  @semax_body (QPvarspecs Chacha20poly1305.qp) (aead_imports3 Chacha20poly1305.CS ++ aead_G3) Chacha20poly1305.CS
    WgNoise.chacha20poly1305.code.f___chacha20poly1305_encrypt __chacha20poly1305_encrypt_spec3.
Proof.
  start_function.
  forward.
  change (Tstruct WgNoise.chacha20poly1305.code.__502 noattr) with t_b3.
  assert_PROP (field_compatible t_b3 [] v_b) by entailer!.
  rewrite enc3_b_data_at_ by auto.
  assert (Pb: isptr v_b) by (destruct H2; auto).
  assert_PROP (field_compatible (tarray tuchar 32) [] v_b) as FCb by entailer!.
  assert_PROP (field_compatible (tarray tuchar (Zlength m + 16)) [] dst) by entailer!.
  rewrite (enc3_split2_ dsh (Zlength m + 16) (Zlength m)) by (auto; rep_lia).
  replace (Zlength m + 16 - Zlength m) with 16 by lia.
  sep_apply (enc3_zero_page_prefix gv 32); [lia|]. flatten_sepcon_in_SEP.
  (* the one-time key *)
  sep_apply (@out3_intro_ Chacha20poly1305.CS Tsh 32 v_b ltac:(lia)).
  forward_call (csh, state, st, Tsh, v_b, Ers, gv _quickproof_zero_page, Zrepeat Byte.zero 32).
  { change (Zlength (Zrepeat Byte.zero 32)) with 32. rep_lia. }
  rewrite enc3_nblocks_32, enc3_otk by auto. change (Zlength (Zrepeat Byte.zero 32)) with 32.
  sep_apply (@out3_elim Chacha20poly1305.CS Tsh (map Vubyte (aead_otk st)) 32 v_b
               ltac:(rewrite Zlength_map; apply enc3_Zlength_otk; auto) FCb).
  sep_apply (wand_frame_elim (prim_bytes Ers (Zrepeat Byte.zero 32) (gv _quickproof_zero_page)) (zero_page gv)).
  (* poly1305_init *)
  assert (Hotk: Zlength (aead_otk st) = 32) by (apply enc3_Zlength_otk; auto).
  remember (aead_otk st) as otk eqn:Eotk. change (enc3_hide (otk = aead_otk st)) in Eotk.
  change (Tstruct _poly1305_desc_ctx noattr) with t_p1305_ctx.
  forward_call enc3_init_sub (Tsh, v_poly1305_state__1, Tsh, v_b, otk).
  (* the associated data (series P22: poly1305_update takes the size_t length itself) *)
  forward_call enc3_update_sub (Tsh, v_poly1305_state__1, otk, @nil byte, ash, ad, a).
  rewrite app_nil_l.
  freeze FR := - (p1305_state _ _ _ _) (zero_page gv).
  forward_if (PROP ()
    LOCAL (temp WgNoise.chacha20poly1305.code._pad0 (gv _quickproof_zero_page);
           lvar WgNoise.chacha20poly1305.code._b t_b3 v_b;
           lvar WgNoise.chacha20poly1305.code._poly1305_state__1 (Tstruct _poly1305_desc_ctx noattr) v_poly1305_state__1;
           gvars gv; temp WgNoise.chacha20poly1305.code._dst dst; temp WgNoise.chacha20poly1305.code._src src;
           temp WgNoise.chacha20poly1305.code._src_len (Vlong (Int64.repr (Zlength m)));
           temp WgNoise.chacha20poly1305.code._ad ad;
           temp WgNoise.chacha20poly1305.code._ad_len (Vlong (Int64.repr (Zlength a)));
           temp WgNoise.chacha20poly1305.code._chacha_state__1 state)
    SEP (p1305_state Tsh otk (a ++ pad16 a) v_poly1305_state__1; zero_page gv; FRZL FR)).
  - assert (Hr: Zlength a mod 16 <> 0).
    { rewrite enc3_and15 in H4 by rep_lia. intro E. rewrite E in H4. apply H4. reflexivity. }
    pose proof (Z.mod_pos_bound (Zlength a) 16).
    sep_apply (@enc3_zero_page_prefix Chacha20poly1305.CS gv (16 - Zlength a mod 16)); [lia|].
    flatten_sepcon_in_SEP.
    forward_call enc3_update_sub (Tsh, v_poly1305_state__1, otk, a, Ers, gv _quickproof_zero_page,
                  Zrepeat Byte.zero (16 - Zlength a mod 16)).
    { go_lower. apply prop_right. simpl. rewrite out3_pad_len64 by rep_lia.
      rewrite Zlength_Zrepeat by lia. reflexivity. }
    { rewrite Zlength_Zrepeat by lia. rep_lia. }
    sep_apply (wand_frame_elim (prim_bytes Ers (Zrepeat Byte.zero (16 - Zlength a mod 16)) (gv _quickproof_zero_page))
                 (zero_page gv)).
    rewrite (enc3_pad16_nz a) by auto.
    entailer!.
  - assert (Hr: Zlength a mod 16 = 0).
    { rewrite enc3_and15 in H4 by rep_lia. pose proof (Z.mod_pos_bound (Zlength a) 16).
      apply (f_equal Int64.unsigned) in H4. rewrite Int64.unsigned_repr in H4 by rep_lia. exact H4. }
    forward. rewrite (enc3_pad16_z a Hr), app_nil_r. entailer!.
  - thaw FR.
    (* the ciphertext *)
    assert (Hst1: Zlength (chacha_advance st 1) = 16) by (rewrite enc3_Zlength_advance; auto).
    assert_PROP (field_compatible (tarray tuchar (Zlength m)) [] dst) as FCm by entailer!.
    sep_apply (@out3_intro_ Chacha20poly1305.CS dsh (Zlength m) dst (Zlength_nonneg m)).
    forward_call (csh, state, chacha_advance st 1, dsh, dst, ssh, src, m).
    assert (Hct: Zlength (chacha_xor 10 (chacha_advance st 1) m) = Zlength m)
      by (apply enc3_Zlength_chacha_xor; auto).
    sep_apply (@out3_elim Chacha20poly1305.CS dsh (map Vubyte (chacha_xor 10 (chacha_advance st 1) m)) (Zlength m) dst
                 ltac:(rewrite Zlength_map; auto) FCm).
    remember (chacha_xor 10 (chacha_advance st 1) m) as ct eqn:Ect. change (enc3_hide (ct = chacha_xor 10 (chacha_advance st 1) m)) in Ect.
    sep_apply (@enc3_prim_bytes_of Chacha20poly1305.CS dsh (Zlength m) ct dst Hct). flatten_sepcon_in_SEP.
    forward_call enc3_update_sub (Tsh, v_poly1305_state__1, otk, a ++ pad16 a, dsh, dst, ct).
    { go_lower. apply prop_right. simpl. rewrite Hct. reflexivity. }
    sep_apply (wand_frame_elim (prim_bytes dsh ct dst) (data_at dsh (tarray tuchar (Zlength m)) (map Vubyte ct) dst)).
    freeze FR := - (p1305_state _ _ _ _) (zero_page gv).
    forward_if (PROP ()
      LOCAL (temp WgNoise.chacha20poly1305.code._pad0 (gv _quickproof_zero_page);
             lvar WgNoise.chacha20poly1305.code._b t_b3 v_b;
             lvar WgNoise.chacha20poly1305.code._poly1305_state__1 (Tstruct _poly1305_desc_ctx noattr) v_poly1305_state__1;
             gvars gv; temp WgNoise.chacha20poly1305.code._dst dst; temp WgNoise.chacha20poly1305.code._src src;
             temp WgNoise.chacha20poly1305.code._src_len (Vlong (Int64.repr (Zlength m)));
             temp WgNoise.chacha20poly1305.code._ad ad;
             temp WgNoise.chacha20poly1305.code._ad_len (Vlong (Int64.repr (Zlength a)));
             temp WgNoise.chacha20poly1305.code._chacha_state__1 state)
      SEP (p1305_state Tsh otk (a ++ pad16 a ++ ct ++ pad16 ct) v_poly1305_state__1; zero_page gv; FRZL FR)).
    + assert (Hr: Zlength m mod 16 <> 0).
      { rewrite enc3_and15 in H4 by rep_lia. intro E. rewrite E in H4. apply H4. reflexivity. }
      pose proof (Z.mod_pos_bound (Zlength m) 16).
      sep_apply (@enc3_zero_page_prefix Chacha20poly1305.CS gv (16 - Zlength m mod 16)); [lia|].
      flatten_sepcon_in_SEP.
      forward_call enc3_update_sub (Tsh, v_poly1305_state__1, otk, (a ++ pad16 a) ++ ct, Ers, gv _quickproof_zero_page,
                    Zrepeat Byte.zero (16 - Zlength m mod 16)).
      { go_lower. apply prop_right. simpl. rewrite out3_pad_len64 by rep_lia.
        rewrite Zlength_Zrepeat by lia. reflexivity. }
      { rewrite Zlength_Zrepeat by lia. rep_lia. }
      sep_apply (wand_frame_elim (prim_bytes Ers (Zrepeat Byte.zero (16 - Zlength m mod 16)) (gv _quickproof_zero_page))
                   (zero_page gv)).
      rewrite (enc3_pad16_nz ct) by (rewrite Hct; auto). rewrite Hct, !app_assoc.
      entailer!.
    + assert (Hr: Zlength m mod 16 = 0).
      { rewrite enc3_and15 in H4 by rep_lia. pose proof (Z.mod_pos_bound (Zlength m) 16).
        apply (f_equal Int64.unsigned) in H4. rewrite Int64.unsigned_repr in H4 by rep_lia. exact H4. }
      forward. rewrite (enc3_pad16_z ct) by (rewrite Hct; auto). rewrite app_nil_r, !app_assoc. entailer!.
    + thaw FR.
      (* the lengths *)
      rewrite (@enc3_data_at_len Chacha20poly1305.CS Tsh 32 (map Vubyte otk) v_b) by (rewrite Zlength_map; auto).
      forward_call (Zlength a, Tsh, v_b, 0, map Vubyte otk).
      { rewrite Zlength_map; lia. }
      rewrite (enc3_lens1 otk (Zlength a) Hotk).
      rewrite Zlength_map, Hotk.
      assert (Hla: Zlength (le64_bytes (Zlength a)) = 8) by reflexivity.
      remember (le64_bytes (Zlength a)) as la eqn:Ela. change (enc3_hide (la = le64_bytes (Zlength a))) in Ela.
      rewrite (@enc3_data_at_len Chacha20poly1305.CS Tsh 32 (map Vubyte (la ++ sublist 8 32 otk)) v_b)
        by (apply enc3_Zlength_L1; auto).
      forward_call (Zlength m, Tsh, v_b, 8, map Vubyte (la ++ sublist 8 32 otk)).
      { go_lower. apply prop_right. simpl. rewrite isptr_offset_val_zero by auto.
        destruct v_b; try contradiction. reflexivity. }
      { rewrite enc3_Zlength_L1 by auto. lia. }
      assert (Hlm: Zlength (le64_bytes (Zlength m)) = 8) by reflexivity.
      remember (le64_bytes (Zlength m)) as lm eqn:Elm. change (enc3_hide (lm = le64_bytes (Zlength m))) in Elm.
      rewrite (enc3_lens2 otk la lm Hotk Hla Hlm).
      rewrite (enc3_Zlength_L1 otk la Hotk Hla).
      assert (Hl16: Zlength (la ++ lm) = 16) by (rewrite Zlength_app; lia).
      assert (Hs16: Zlength (sublist 16 32 otk) = 16) by (rewrite Zlength_sublist; lia).
      rewrite (@enc3_split2 Chacha20poly1305.CS Tsh 32 16) by (auto; try lia; rewrite Zlength_app, !Zlength_map; lia).
      destruct (enc3_sub16 _ _ Hl16 Hs16) as [-> ->]. change (32 - 16) with 16. flatten_sepcon_in_SEP.
      rewrite (@enc3_prim_bytes_fold Chacha20poly1305.CS Tsh 16 (la ++ lm) v_b) by (auto; lia).
      forward_call enc3_update_sub (Tsh, v_poly1305_state__1, otk, a ++ pad16 a ++ ct ++ pad16 ct, Tsh, v_b,
                    la ++ lm).
      { go_lower. apply prop_right. simpl. rewrite Hl16, isptr_offset_val_zero by auto. reflexivity. }
      (* the tag *)
      forward_call enc3_final_sub (Tsh, v_poly1305_state__1, otk, (a ++ pad16 a ++ ct ++ pad16 ct) ++ la ++ lm, dsh,
                    offset_val (Zlength m) dst).
      { go_lower. apply prop_right. simpl. rewrite sem_add_pl_ptr_special' by (auto; rep_lia).
        change (sizeof tuchar) with 1. rewrite Z.mul_1_l. reflexivity. }
      (* cleanup *)
      sep_apply (data_at_data_at_ csh t_chacha_state
                   (map Vint (chacha_advance (chacha_advance st 1) (chacha_nblocks (Zlength m)))) state).
      forward_call enc3_zeroize_sub (csh, state).
      assert (Hs16': Zlength (map Vubyte (sublist 16 32 otk)) = 16) by (rewrite Zlength_map; auto).
      sep_apply (enc3_b_join Tsh (la ++ lm) (map Vubyte (sublist 16 32 otk)) v_b Hl16 Hs16' FCb).
      forward_call (Tsh, v_b, 32).
      (* the postcondition *)
      unfold enc3_hide in Eotk, Ect, Ela, Elm.
      sep_apply (data_at_data_at_ Tsh (tarray tuchar 32) (Zrepeat (Vubyte Byte.zero) 32) v_b).
      rewrite <- (enc3_b_data_at_ v_b H2).
      assert (Hmac: (a ++ pad16 a ++ ct ++ pad16 ct) ++ la ++ lm = aead_mac_data a ct)
        by (subst la lm; unfold aead_mac_data; rewrite Hct, <- !app_assoc; reflexivity).
      rewrite Hmac.
      assert (Htag: Zlength (poly1305_tag otk (aead_mac_data a ct)) = 16) by reflexivity.
      sep_apply (enc3_dst_join dsh (Zlength m) ct (poly1305_tag otk (aead_mac_data a ct)) dst Hct Htag H3).
      replace (ct ++ poly1305_tag otk (aead_mac_data a ct)) with (aead_enc_st st a m) by (subst; reflexivity).
      change (Tstruct _poly1305_desc_ctx noattr) with t_p1305_ctx.
      clear Eotk Ect Ela Elm.
      entailer!.
Qed.

End Enc3.
