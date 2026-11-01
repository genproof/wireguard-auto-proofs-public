(* law config_any: helpers of hcf5_P5a_ok.
   q's handshake memory (data_at_ t_hs at Noise.CS) opened at one field (a store or nondet_bytes target, at the
   world compspecs W) and closed again as data_at_; the device split into its identity and the rest; the pure
   facts of the pool after q's entry joins it. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.config_any.hcf5_world.
Require Import WgNoise.proof.harness.config_any.hcf5_defs.
Require Import WgNoise.proof.harness.config_any.hcf5_pure.
Require WgNoise.harness.x_config_any.code.
Local Open Scope logic.

#[local] Instance hcf5_p5a_cce : change_composite_env Noise.CS W_config_any.
Proof. make_cs_preserve Noise.CS W_config_any. Defined.

Lemma hcf5_p5a_hsW q : @field_compatible Noise.CS t_peer [] q ->
  @data_at_ Noise.CS Tsh t_hs (hs_addr q) = @field_at_ W_config_any Tsh t_peer [StructField I._handshake] q.
Proof.
  intros Hfc.
  rewrite <- (@field_at__change_composite Noise.CS W_config_any _ Tsh t_peer [StructField I._handshake])
    by reflexivity.
  rewrite field_at__data_at_.
  f_equal. unfold field_address. rewrite if_true by auto with field_compatible. reflexivity.
Qed.

Lemma hcf5_p5a_fcW q : @field_compatible Noise.CS t_peer [] q -> @field_compatible W_config_any t_peer [] q.
Proof.
  intros H. apply (@field_compatible_change_composite Noise.CS W_config_any _ t_peer); [reflexivity | exact H].
Qed.

Section W.
#[local] Existing Instance W_config_any.

Lemma hcf5_p5a_open q gfs1 :
  legal_nested_field t_peer (gfs1 ++ [StructField I._handshake]) ->
  @field_compatible Noise.CS t_peer [] q ->
  @data_at_ Noise.CS Tsh t_hs (hs_addr q) |--
  field_at_ Tsh t_peer (gfs1 ++ [StructField I._handshake]) q *
  (ALL v: reptype (nested_field_type t_peer (gfs1 ++ [StructField I._handshake])),
     field_at Tsh t_peer (gfs1 ++ [StructField I._handshake]) v q -* @data_at_ Noise.CS Tsh t_hs (hs_addr q)).
Proof.
  intros Hl Hfc.
  rewrite (hcf5_p5a_hsW _ Hfc). apply hcf5_p5a_fcW in Hfc.
  unfold field_at_ at 1.
  pose proof (nested_field_type_nested_field_type t_peer [StructField I._handshake] gfs1) as E.
  set (d := default_val (nested_field_type t_peer [StructField I._handshake])).
  eapply derives_trans;
    [apply (nested_field_ramif' Tsh t_peer [StructField I._handshake] gfs1 d
              (eq_rect _ reptype (proj_reptype _ gfs1 d) _ E) q) |].
  { clear. revert E. generalize (nested_field_type t_peer (gfs1 ++ [StructField I._handshake])).
    intros t' E. subst t'. apply JMeq_refl. }
  { exact Hl. }
  apply sepcon_derives; [apply field_at_field_at_ |].
  apply allp_right; intros v.
  apply (allp_left _ v).
  apply (allp_left _ (eq_rect_r reptype v E)).
  assert (HJ: JMeq v (eq_rect_r reptype v E)) by (apply JMeq_sym; apply eq_rect_r_JMeq).
  eapply derives_trans; [apply andp_right; [apply prop_right; exact HJ | apply derives_refl] |].
  eapply derives_trans; [apply modus_ponens |].
  apply wand_derives; [apply derives_refl | apply field_at_field_at_].
Qed.

Lemma hcf5_p5a_close {A: Type} (P: A -> mpred) (v: A) (X: mpred) :
  P v * (ALL v': A, P v' -* X) |-- X.
Proof.
  eapply derives_trans; [apply sepcon_derives; [apply derives_refl | apply (allp_left _ v); apply derives_refl] |].
  apply wand_frame_elim.
Qed.

Lemma hcf5_p5a_fa q gfs : field_compatible t_peer gfs q ->
  field_address t_peer gfs q = offset_val (nested_field_offset t_peer gfs) q.
Proof. intros. unfold field_address. rewrite if_true by auto. reflexivity. Qed.

(* the three byte arrays of q's handshake that nondet_bytes fills: offsets 136, 200, 232 in q *)
Ltac hcf5_p5a_arr_tac :=
  intros Hfc; apply hcf5_p5a_fcW in Hfc; simpl app;
  rewrite field_at__data_at_, hcf5_p5a_fa by auto with field_compatible; reflexivity.
Ltac hcf5_p5a_arr_tac' :=
  intros Hfc; apply hcf5_p5a_fcW in Hfc; simpl app;
  rewrite field_at_data_at, hcf5_p5a_fa by auto with field_compatible; reflexivity.

Lemma hcf5_p5a_rs_ q : @field_compatible Noise.CS t_peer [] q ->
  field_at_ Tsh t_peer ([StructField I._remote_static] ++ [StructField I._handshake]) q =
  data_at_ Tsh (tarray tuchar 32) (offset_val 136 q).
Proof. hcf5_p5a_arr_tac. Qed.
Lemma hcf5_p5a_rs q v : @field_compatible Noise.CS t_peer [] q ->
  field_at Tsh t_peer ([StructField I._remote_static] ++ [StructField I._handshake]) v q =
  data_at Tsh (tarray tuchar 32) v (offset_val 136 q).
Proof. hcf5_p5a_arr_tac'. Qed.
Lemma hcf5_p5a_ss_ q : @field_compatible Noise.CS t_peer [] q ->
  field_at_ Tsh t_peer ([StructField I._precomputed_static_static] ++ [StructField I._handshake]) q =
  data_at_ Tsh (tarray tuchar 32) (offset_val 200 q).
Proof. hcf5_p5a_arr_tac. Qed.
Lemma hcf5_p5a_ss q v : @field_compatible Noise.CS t_peer [] q ->
  field_at Tsh t_peer ([StructField I._precomputed_static_static] ++ [StructField I._handshake]) v q =
  data_at Tsh (tarray tuchar 32) v (offset_val 200 q).
Proof. hcf5_p5a_arr_tac'. Qed.
Lemma hcf5_p5a_psk_ q : @field_compatible Noise.CS t_peer [] q ->
  field_at_ Tsh t_peer ([StructField I._preshared_key] ++ [StructField I._handshake]) q =
  data_at_ Tsh (tarray tuchar 32) (offset_val 232 q).
Proof. hcf5_p5a_arr_tac. Qed.
Lemma hcf5_p5a_psk q v : @field_compatible Noise.CS t_peer [] q ->
  field_at Tsh t_peer ([StructField I._preshared_key] ++ [StructField I._handshake]) v q =
  data_at Tsh (tarray tuchar 32) v (offset_val 232 q).
Proof. hcf5_p5a_arr_tac'. Qed.

End W.

#[local] Instance hcf5_p5a_cceH : change_composite_env HCS W_config_any.
Proof. make_cs_preserve HCS W_config_any. Defined.
#[local] Instance hcf5_p5a_cceNH : change_composite_env Noise.CS HCS.
Proof. make_cs_preserve Noise.CS HCS. Defined.

(* nondet_bytes's result as a Noise.CS byte buffer *)
Lemma hcf5_p5a_nd sh bs p : Zlength bs = 32 -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W_config_any sh (tarray tuchar 32) (map (fun b => Vint (Int.repr b)) bs) p =
  bytes_at sh (map Byte.repr bs) p.
Proof.
  intros Hn Hb. unfold bytes_at. rewrite Zlength_map, Hn.
  rewrite <- (@data_at_change_composite Noise.CS W_config_any _ sh (tarray tuchar 32) _ _ (JMeq_refl _))
    by prove_cs_preserve_type.
  f_equal. unfold bytes. rewrite map_map.
  clear Hn. induction Hb; simpl; [reflexivity |]. f_equal; [| assumption].
  unfold Vubyte. rewrite Byte.unsigned_repr by (unfold Byte.max_unsigned in *; simpl in *; lia). reflexivity.
Qed.

Lemma hcf5_p5a_bh sh B p : bytes_at sh B p = hbytes sh B p.
Proof.
  unfold bytes_at, hbytes.
  apply equal_f.
  apply (@data_at_change_composite Noise.CS HCS _ sh (tarray tuchar (Zlength B)) _ _ (JMeq_refl _)).
  prove_cs_preserve_type.
Qed.

Lemma hcf5_p5a_outW sh p : @data_at_ W_config_any sh (tarray tuchar 32) p = hout sh 32 p.
Proof.
  unfold hout. symmetry. apply equal_f.
  apply (@data_at__change_composite HCS W_config_any _ sh (tarray tuchar 32)). prove_cs_preserve_type.
Qed.

Lemma hcf5_p5a_and1 x : Int.and x (Int.repr 1) =
  if Int.eq (Int.and x (Int.repr 1)) Int.zero then Int.zero else Int.one.
Proof.
  assert (E: Int.and x (Int.repr 1) = Int.repr (Int.unsigned x mod 2)).
  { unfold Int.and. f_equal. rewrite Int.unsigned_repr by (cbv; split; congruence).
    change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. }
  rewrite E.
  assert (H: Int.unsigned x mod 2 = 0 \/ Int.unsigned x mod 2 = 1)
    by (pose proof (Z.mod_pos_bound (Int.unsigned x) 2 ltac:(lia)); lia).
  destruct H as [H | H]; rewrite H; reflexivity.
Qed.

Section NoiseCS.
#[local] Existing Instance Noise.CS.

(* the device without its identity *)
Definition hcf5_p5a_drest (sh: share) (wg: val) (D: device) : mpred :=
  !! field_compatible t_dev [] wg &&
  (field_at sh t_dev [StructField I._dev] (d_dev D) wg *
   checker_rep sh (cc_addr wg) (d_cc D) *
   field_at sh t_dev [StructField I._peer_hashtable] (d_ptab D) wg *
   field_at sh t_dev [StructField I._index_hashtable] (d_itab D) wg).

Lemma hcf5_p5a_dev_split sh wg D :
  device_rep sh wg D = identity_rep sh (id_addr wg) (d_id D) * hcf5_p5a_drest sh wg D.
Proof.
  unfold device_rep, hcf5_p5a_drest. rewrite sepcon_andp_prop.
  f_equal. apply pred_ext; cancel.
Qed.
End NoiseCS.

(* ---- q's entry joins the pool: nothing else of the table's view changes ---- *)
Lemma hcf5_p5a_sfind (T: tstate) a sh E x : x <> a -> sfind (t_D (t_add T a sh E)) x = sfind (t_D T) x.
Proof. intros Hx. unfold t_add; simpl. destruct (EqDec_val a x); [congruence | reflexivity]. Qed.

Lemma hcf5_p5a_ed (T: tstate) a sh E x : x <> a -> t_entry_d (t_add T a sh E) x = t_entry_d T x.
Proof. intros Hx. unfold t_entry_d, t_entry. rewrite hcf5_p5a_sfind by auto. reflexivity. Qed.

Lemma hcf5_p5a_tsh (T: tstate) a sh E x : x <> a -> hcf5_tsh (t_add T a sh E) x = hcf5_tsh T x.
Proof. intros Hx. unfold hcf5_tsh. rewrite hcf5_p5a_sfind by auto. reflexivity. Qed.

Lemma hcf5_p5a_snap (T: tstate) a sh E p P : hs_addr p <> a ->
  hs_snap_cur (t_add T a sh E) p P = hs_snap_cur T p P.
Proof. intros Hx. unfold hs_snap_cur, snap_of. rewrite hcf5_p5a_ed by auto. reflexivity. Qed.

Lemma hcf5_p5a_kent_same (T: tstate) a sh E e : ke_addr e <> a -> kent_same (t_add T a sh E) e = kent_same T e.
Proof. intros Hx. unfold kent_same, kent_eqb_cur. rewrite hcf5_p5a_ed by auto. reflexivity. Qed.

Lemma hcf5_p5a_kent_ptrs (T: tstate) a sh E e : ke_addr e <> a -> kent_ptrs (t_add T a sh E) e = kent_ptrs T e.
Proof. intros Hx. unfold kent_ptrs. rewrite hcf5_p5a_ed by auto. reflexivity. Qed.

Lemma hcf5_p5a_forallb {X: Type} (f g: X -> bool) (l: list X) :
  (forall x, In x l -> f x = g x) -> forallb f l = forallb g l.
Proof.
  induction l as [|x l IH]; intros Hfg; simpl; [reflexivity |].
  rewrite (Hfg x (or_introl eq_refl)), IH by (intros; apply Hfg; right; auto). reflexivity.
Qed.

Lemma hcf5_p5a_inv R L S w D P T KE :
  hcf5_inv R L S w D P T KE false -> itable_wf T -> ~ In (hs_addr (l_q L)) (saddrs (t_D T)) ->
  hcf5_inv R L S w D P (t_add T (hs_addr (l_q L)) Tsh (mkEntry (l_q L) IDX_HANDSHAKE Int.zero)) KE true.
Proof.
  unfold hcf5_inv. intros (Hr & Hb & Hw & Hd & Hp & Hs & HT & Hk) Hwf Hn.
  set (a := hs_addr (l_q L)) in *.
  destruct HT as (Hsa & HKE & Hpt & Hpe & _).
  assert (Hin: forall x, In x (map ke_addr KE) -> x <> a).
  { intros x Hx Ha. subst x. apply Hn. rewrite Hsa. simpl. apply in_or_app. left. exact Hx. }
  assert (Hpa: hs_addr (l_p L) <> a).
  { intros Ha. apply Hn. rewrite <- Ha, Hsa. simpl. apply in_or_app. right. left. reflexivity. }
  split; [exact Hr |]. split; [exact Hb |]. split; [exact Hw |]. split; [exact Hd |]. split; [exact Hp |].
  split; [exact Hs |]. split.
  - unfold hcf5_T_ok. split; [| split; [| split; [| split]]].
    + unfold t_add. simpl. rewrite Hsa. reflexivity.
    + rewrite Forall_forall in HKE |- *. intros e He.
      assert (Hea: ke_addr e <> a) by (apply Hin; apply in_map; exact He).
      rewrite hcf5_p5a_tsh, hcf5_p5a_ed by exact Hea. apply HKE; exact He.
    + rewrite hcf5_p5a_tsh by exact Hpa. exact Hpt.
    + rewrite hcf5_p5a_ed by exact Hpa. exact Hpe.
    + intros _. unfold hcf5_tsh, t_entry_d, t_entry, t_add. simpl.
      match goal with |- context [EqDec_val ?x ?y] => destruct (EqDec_val x y) as [_ | C]; [| unfold a in C; congruence] end. split; [reflexivity | split; [reflexivity |]].
      intros HL. apply Hn. destruct Hwf as (_ & Hincl & _). apply Hincl. exact HL.
  - unfold hcf5_ksnap_ok in *. rewrite Forall_forall in Hk |- *. intros e He.
    assert (Hea: ke_addr e <> a) by (apply Hin; apply in_map; exact He).
    destruct (Hk e He) as [Hsn Hv]. split; [exact Hsn |].
    rewrite hcf5_p5a_kent_ptrs by exact Hea.
    eapply Forall_impl; [| exact Hv]. intros x [Hx | Hx]; [left; exact Hx | right].
    destruct Hx as [Hx | Hx]; [left; exact Hx | right; right; exact Hx].
Qed.

Lemma hcf5_p5a_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 a sh E :
  hcf5_T_ok L KE false T -> ~ In a (saddrs (t_D T)) ->
  hcf5_same L D P T KE S w D0 sn0 P0 r0 S0 w0 h0 ->
  hcf5_same L D P (t_add T a sh E) KE S w D0 sn0 P0 r0 S0 w0 h0.
Proof.
  intros (Hsa & _) Hn. unfold hcf5_same. intros (Hd & Hs & Hp & Hr & Hsh & Hk & Hh).
  assert (Hpa: hs_addr (l_p L) <> a).
  { intros Ha. apply Hn. rewrite <- Ha, Hsa. simpl. apply in_or_app. right. left. reflexivity. }
  split; [exact Hd |]. split; [rewrite hcf5_p5a_snap by exact Hpa; exact Hs |].
  split; [exact Hp |]. split; [exact Hr |]. split; [exact Hsh |]. split; [| exact Hh].
  rewrite <- Hk. apply hcf5_p5a_forallb. intros e He. apply hcf5_p5a_kent_same.
  intros Ha. apply Hn. rewrite <- Ha, Hsa. simpl. apply in_or_app. left. apply in_map. exact He.
Qed.
