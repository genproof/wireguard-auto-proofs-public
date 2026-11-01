(* law consume_initiation_any: segment A of phase P5 = statements 15..17: fill_init(msg); mode = nondet_u8() % 3; the mode block (A's initiation by the model, mode 2: one byte xor'ed). Port of v1's hci3_P5.v.
   States: hci5_defs.v (S4), hci5_p5_defs.v (Q17, Q18). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_cut.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_ts.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_model.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_globals.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_spec.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_defs.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_conv.
Require Import WgNoise.proof.harness.consume_initiation_any.hci5_p5_defs.
Require WgNoise.harness.x_consume_initiation_any.code.

#[local] Existing Instance W_consume_initiation_any.
Local Open Scope Z_scope.

Notation W := W_consume_initiation_any.

#[local] Instance hci5_p5A_cce_N : change_composite_env Noise.CS W_consume_initiation_any.
Proof. make_cs_preserve Noise.CS W_consume_initiation_any. Defined.
#[local] Instance hci5_p5A_cce_H : change_composite_env HCS W_consume_initiation_any.
Proof. make_cs_preserve HCS W_consume_initiation_any. Defined.

Lemma hci5_p5A_cs_eq {cs1 cs2} {CCE: change_composite_env cs1 cs2} (sh: share) (t: type) (v1: @reptype cs1 t)
  (v2: @reptype cs2 t) (p: val) :
  JMeq v1 v2 -> cs_preserve_type cs1 cs2 (coeq _ _) t = true ->
  @data_at cs1 sh t v1 p = @data_at cs2 sh t v2 p.
Proof. intros. exact (f_equal (fun f => f p) (@data_at_change_composite cs1 cs2 CCE sh t v1 v2 H H0)). Qed.

(* compspecs conversions *)
Lemma hci5_p5A_init_W sh M m :
  @data_at Noise.CS sh t_init (init_val M) m = @data_at W sh t_init (init_val M) m.
Proof. apply (@hci5_p5A_cs_eq Noise.CS W _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hci5_p5A_mident_W sh I p :
  @data_at HCS sh t_mident (mident_val I) p = @data_at W sh t_mident (mident_val I) p.
Proof. apply (@hci5_p5A_cs_eq HCS W _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hci5_p5A_minit_W sh E encs enct ep ck h p :
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  @data_at W sh t_minit (minit_val E encs enct ep ck h) p.
Proof. apply (@hci5_p5A_cs_eq HCS W _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hci5_p5A_hb_W sh bs p :
  hbytes sh bs p = @data_at W sh (tarray tuchar (Zlength bs)) (bytes bs) p.
Proof. unfold hbytes. apply (@hci5_p5A_cs_eq HCS W _); [apply JMeq_refl | prove_cs_preserve_type]. Qed.

Lemma hci5_p5A_hb_out sh bs p : hbytes sh bs p |-- hout sh (Zlength bs) p.
Proof. unfold hbytes, hout. apply data_at_data_at_. Qed.

(* the fields of an identity *)
Lemma hci5_p5A_mident_split sh I p : Zlength (mi_pub I) = 32 ->
  @data_at HCS sh t_mident (mident_val I) p =
  (@field_at W sh t_mident [StructField HC._priv] (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (@field_address W t_mident [StructField HC._pub] p) *
   @field_at W sh t_mident [StructField HC._ok] (Vint (if mi_ok I then Int.one else Int.zero)) p)%logic.
Proof.
  intros Hl. rewrite hci5_p5A_mident_W, hci5_p5A_hb_W, Hl. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_mident [StructField HC._pub]). apply pred_ext; cancel.
Qed.

(* the fields of the model's message *)
Lemma hci5_p5A_minit_split sh E encs enct ep ck h p :
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  @data_at HCS sh t_minit (minit_val E encs enct ep ck h) p =
  (hbytes sh E (@field_address W t_minit [StructField HC._ephemeral] p) *
   hbytes sh encs (@field_address W t_minit [StructField HC._enc_static] p) *
   hbytes sh enct (@field_address W t_minit [StructField HC._enc_timestamp] p) *
   @field_at W sh t_minit [StructField HC._eph_priv] (bytes ep) p *
   @field_at W sh t_minit [StructField HC._st] (bytes ck, bytes h) p)%logic.
Proof.
  intros H1 H2 H3. rewrite hci5_p5A_minit_W, !hci5_p5A_hb_W, H1, H2, H3. unfold_data_at (data_at _ _ _ p).
  rewrite (field_at_data_at sh t_minit [StructField HC._ephemeral]).
  rewrite (field_at_data_at sh t_minit [StructField HC._enc_static]).
  rewrite (field_at_data_at sh t_minit [StructField HC._enc_timestamp]). apply pred_ext; cancel.
Qed.

(* the fields of a message *)
Lemma hci5_p5A_init_split sh ty se eph encs enct mac1 mac2 m :
  Zlength eph = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  @data_at Noise.CS sh t_init (init_val (mkIM ty se eph encs enct mac1 mac2)) m =
  (@field_at W sh t_init [StructField HC._header] (Vint ty) m *
   @field_at W sh t_init [StructField HC._sender_index] (Vint se) m *
   hbytes sh eph (@field_address W t_init [StructField HC._unencrypted_ephemeral] m) *
   hbytes sh encs (@field_address W t_init [StructField HC._encrypted_static] m) *
   hbytes sh enct (@field_address W t_init [StructField HC._encrypted_timestamp] m) *
   @field_at W sh t_init [StructField HC._macs] (bytes mac1, bytes mac2) m)%logic.
Proof.
  intros H1 H2 H3. rewrite hci5_p5A_init_W, !hci5_p5A_hb_W, H1, H2, H3. unfold_data_at (data_at _ _ _ m).
  rewrite (field_at_data_at sh t_init [StructField HC._unencrypted_ephemeral]).
  rewrite (field_at_data_at sh t_init [StructField HC._encrypted_static]).
  rewrite (field_at_data_at sh t_init [StructField HC._encrypted_timestamp]). apply pred_ext; cancel.
Qed.

Lemma hci5_p5A_mident_join sh I p : Zlength (mi_pub I) = 32 ->
  (@field_at W sh t_mident [StructField HC._priv] (bytes (mi_priv I)) p *
   hbytes sh (mi_pub I) (@field_address W t_mident [StructField HC._pub] p) *
   @field_at W sh t_mident [StructField HC._ok] (Vint (if mi_ok I then Int.one else Int.zero)) p
   |-- @data_at HCS sh t_mident (mident_val I) p)%logic.
Proof. intros Hl. rewrite (hci5_p5A_mident_split sh I p Hl). apply derives_refl. Qed.

Lemma hci5_p5A_minit_join sh E encs enct ep ck h p :
  Zlength E = 32 -> Zlength encs = 48 -> Zlength enct = 28 ->
  (hbytes sh E (@field_address W t_minit [StructField HC._ephemeral] p) *
   hbytes sh encs (@field_address W t_minit [StructField HC._enc_static] p) *
   hbytes sh enct (@field_address W t_minit [StructField HC._enc_timestamp] p) *
   @field_at W sh t_minit [StructField HC._eph_priv] (bytes ep) p *
   @field_at W sh t_minit [StructField HC._st] (bytes ck, bytes h) p
   |-- @data_at_ HCS sh t_minit p)%logic.
Proof.
  intros H1 H2 H3. rewrite <- (hci5_p5A_minit_split sh E encs enct ep ck h p H1 H2 H3).
  apply data_at_data_at_.
Qed.

Lemma hci5_p5A_init_join sh ty se eph encs enct mac1 mac2 m :
  Zlength eph = 32 -> Zlength encs = 48 -> Zlength enct = 28 -> Zlength mac1 = 16 -> Zlength mac2 = 16 ->
  (@field_at W sh t_init [StructField HC._header] (Vint ty) m *
   @field_at W sh t_init [StructField HC._sender_index] (Vint se) m *
   hbytes sh eph (@field_address W t_init [StructField HC._unencrypted_ephemeral] m) *
   hbytes sh encs (@field_address W t_init [StructField HC._encrypted_static] m) *
   hbytes sh enct (@field_address W t_init [StructField HC._encrypted_timestamp] m) *
   @field_at W sh t_init [StructField HC._macs] (bytes mac1, bytes mac2) m
   |-- init_rep sh m (mkIM ty se eph encs enct mac1 mac2))%logic.
Proof.
  intros H1 H2 H3 H4 H5. unfold init_rep.
  rewrite (hci5_p5A_init_split sh ty se eph encs enct mac1 mac2 m H1 H2 H3).
  apply andp_right; [apply prop_right; unfold im_ok; simpl; auto | apply derives_refl].
Qed.

Lemma hci5_p5A_map_Vint (l: list Z) : Forall (fun b => 0 <= b <= Byte.max_unsigned) l ->
  map (fun b => Vint (Int.repr b)) l = bytes (map Byte.repr l).
Proof.
  induction l as [| a l IH]; intros Hl; [reflexivity |].
  inversion Hl; subst. unfold bytes in *; simpl. rewrite IH by auto.
  unfold Vubyte. rewrite Byte.unsigned_repr by rep_lia. reflexivity.
Qed.

(* nondet_bytes's result (world) as an hbytes buffer (HCS) *)
Lemma hci5_p5A_nd (bs: list Z) n p :
  Zlength bs = n -> Forall (fun b => 0 <= b <= Byte.max_unsigned) bs ->
  @data_at W Tsh (tarray tuchar n) (map (fun b => Vint (Int.repr b)) bs) p = hbytes Tsh (map Byte.repr bs) p.
Proof.
  intros Hl Hr. rewrite hci5_p5A_hb_W, Zlength_map, Hl, hci5_p5A_map_Vint by auto. reflexivity.
Qed.

Lemma hci5_p5A_Znth_bytes l i : 0 <= i < Zlength l -> Znth i (bytes l) = Vubyte (Znth i l).
Proof. intros Hi. unfold bytes. rewrite Znth_map by lia. reflexivity. Qed.

(* one byte of a buffer xor'ed (the stored value is cast to unsigned char) *)
Lemma hci5_p5A_upd_bytes l i x : 0 <= i < Zlength l ->
  upd_Znth i (bytes l) (Vint (Int.zero_ext 8 x)) = bytes (upd_Znth i l (Byte.repr (Int.unsigned x))).
Proof.
  intros Hi. unfold bytes. rewrite <- upd_Znth_map. f_equal. unfold Vubyte. f_equal.
  rewrite Byte.unsigned_repr_eq. rewrite <- (Int.repr_unsigned (Int.zero_ext 8 x)).
  rewrite Int.zero_ext_mod by (cbn; lia). reflexivity.
Qed.

Lemma hci5_p5A_clamp_len s : Zlength s = 32 -> Zlength (clamp s) = 32.
Proof. intros Hl. unfold clamp. rewrite !upd_Znth_Zlength; rewrite ?upd_Znth_Zlength; lia. Qed.

(* the shim's state, opened at the real clock (main loads wg_shim_real_sec / nsec) *)
Definition hci5_p5A_shim_rest (gv: globals) (S: shim) (w: list int64) : mpred :=
  (@data_at Noise.CS Ews tulong (Vlong (s_boot S)) (gv _wg_shim_boottime_ns) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_log S)) (gv _wg_shim_random_log) *
   @data_at Noise.CS Ews (tarray tuchar 32) (bytes (s_logprev S)) (gv _wg_shim_random_log_prev) *
   @data_at Noise.CS Ews tuint (Vint (s_u32 S)) (gv _wg_shim_random_u32) *
   @data_at Noise.CS Ews tulong (Vlong (s_allocs S)) (gv _wg_shim_allocs) *
   @data_at Noise.CS Ews tulong (Vlong (s_fails S)) (gv _wg_shim_alloc_failures) *
   @data_at Noise.CS Ews tulong (Vlong (s_frees S)) (gv _wg_shim_frees) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_failnext S)) (gv _wg_shim_fail_next_alloc) *
   @data_at Noise.CS Ews tulong (Vlong (s_released S)) (gv _wg_shim_peer_released) *
   @data_at Noise.CS Ews tbool (Val.of_bool (s_rlallow S)) (gv _wg_shim_ratelimit_allow) *
   refwarn4 gv w)%logic.

Lemma hci5_p5A_shim_open gv S w :
  shim_state4 gv S w =
  (!! shim_ok S && (@data_at W Ews tlong (Vlong (s_rsec S)) (gv HC._wg_shim_real_sec) *
                    @data_at W Ews tlong (Vlong (s_rnsec S)) (gv HC._wg_shim_real_nsec) *
                    hci5_p5A_shim_rest gv S w))%logic.
Proof.
  unfold shim_state4, shim_core, hci5_p5A_shim_rest.
  rewrite <- (hci5_p5A_cs_eq (cs1 := Noise.CS) (cs2 := W) Ews tlong (Vlong (s_rsec S)) (Vlong (s_rsec S)))
    by (apply JMeq_refl || reflexivity).
  rewrite <- (hci5_p5A_cs_eq (cs1 := Noise.CS) (cs2 := W) Ews tlong (Vlong (s_rnsec S)) (Vlong (s_rnsec S)))
    by (apply JMeq_refl || reflexivity).
  rewrite sepcon_andp_prop'. f_equal. apply pred_ext; cancel.
Qed.

(* a node of the list is a valid pointer (the comparison na != NULL) *)
Lemma hci5_p5A_node_valid NS : forall l a, In a (map hn_addr NS) ->
  hnodes_rep4 W_consume_initiation_any l NS |-- valid_pointer a.
Proof.
  induction NS as [| N NS IH]; intros l a Hin; [contradiction |].
  simpl in Hin. simpl hnodes_rep4. Intros nx. destruct Hin as [<- | Hin].
  - subst l. entailer!.
  - sep_apply (IH nx a Hin). entailer!.
Qed.

Lemma hci5_p5A_ts_in t ts : Zlength t = 12 -> (hbytes Tsh t ts |-- hci5_p5_tsrep true ts)%logic.
Proof. intros Hl. unfold hci5_p5_tsrep. Exists t. entailer!. Qed.

Lemma hci5_p5A_c_true md na :
  (if Int.eq md Int.zero then Int.zero else if eq_dec na nullval then Int.zero else Int.one) <> Int.zero ->
  hci5_p5_c md na = true.
Proof. unfold hci5_p5_c. destruct (Int.eq md Int.zero); [tauto |]. destruct (eq_dec na nullval); tauto. Qed.

Lemma hci5_p5A_c_false md na :
  (if Int.eq md Int.zero then Int.zero else if eq_dec na nullval then Int.zero else Int.one) = Int.zero ->
  hci5_p5_c md na = false.
Proof.
  unfold hci5_p5_c. destruct (Int.eq md Int.zero); [auto |]. destruct (eq_dec na nullval); [auto |].
  intros Hn. discriminate.
Qed.

Section P5A.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* after the creation block: msg holds some well-formed message, ts m_tai64n's 12 bytes *)
Definition hci5_p5A_Q1 (gv: globals) (L: hci5_loc) (FR: mpred) (R: hci5_run) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head na: val) (KE: list kent4) (m: val) (md: int)
  : environ -> mpred :=
  EX M: init_msg, EX S: shim,
  PROPx [im_ok M]
  (LOCALx ([temp HC._mode (Vint md); temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L);
          hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_p5_scr L (hci5_p5_tsrep true (l_ts L))))).

(* after the mode block *)
Definition hci5_p5A_Q (gv: globals) (L: hci5_loc) (FR: mpred) (R: hci5_run) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head na: val) (KE: list kent4) (m: val) (md: int)
  : environ -> mpred :=
  EX M: init_msg, EX S: shim,
  PROPx [im_ok M]
  (LOCALx ([temp HC._mode (Vint md); temp HC._na na; temp HC._kes (hci5_khead KE); temp HC._msg m] ++
           hci5_lvars gv L)
  (SEPx (hci5_world x25519 R L NS NS T head ++
         [peers_rep PS; kents_rep W (hci5_khead KE) KE; hout Tsh 148 (l_img L);
          hci5_tok t_init m; init_rep Ews m M] ++
         hci5_globs gv S w FR ++ hci5_snaps0 L ++ hci5_p5_scr L (hci5_p5_tsrep (hci5_p5_c md na) (l_ts L))))).

Lemma hci5_p5A_cinit_len SPUB RPUB SS ERAW TS E encs enct ep ck h :
  x25519_props x25519 -> aead_props aead_enc aead_dec ->
  m_create_initiation_model x25519 aead_enc SPUB RPUB SS ERAW TS = Some (E, encs, enct, ep, ck, h) ->
  Zlength E = 32 /\ Zlength encs = Zlength SPUB + 16 /\ Zlength enct = Zlength TS + 16.
Proof.
  intros Hx Ha Hm. unfold m_create_initiation_model in Hm.
  repeat match type of Hm with context [if ?c then _ else _] => destruct c end; try discriminate.
  inversion Hm; subst. rewrite !(aead_enc_length _ _ Ha). auto.
Qed.

Lemma hci5_p5_A_ok {Espec: OracleKind} gv L FR :
  hci5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hci5_Delta x25519 aead_enc aead_dec) (hci5_S4 x25519 gv L FR) (hci5_seql (hci5_l 15 3))
    (overridePost (hci5_p5_Q17 x25519 gv L FR) (hci5_R gv)).
Proof.
  intros HH.
  match goal with |- semax _ _ ?c _ =>
    let c' := eval cbv beta iota delta [hci5_seql hci5_l firstn skipn hci5_stmts] in c in change c with c' end.
  unfold hci5_S4, hci5_Delta, hci5_R. simplify_func_tycontext. abbreviate_semax.
  Intros R S w NS PS T head na KE m.
  unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
  forward_call (Ews, m). Intros M.
  forward_call tt. Intros b.
  forward.
  { entailer!. match goal with Hc: _ /\ Int.repr 3 = Int.mone |- _ => destruct Hc as [_ Hc]; discriminate end. }
  destruct H0 as (Hpok & Hwf & Hch & Hnp & Hna & HTok & Hsl).
  forward_if (temp HC._t'11 (Vint (if Int.eq (Int.mods (Int.repr b) (Int.repr 3)) Int.zero then Int.zero
                                  else if eq_dec na nullval then Int.zero else Int.one))).
  { forward.
    { destruct Hna as [-> | Hin]; [entailer! |].
      entailer!. pull_left (hnodes_rep4 W (hci5_head NS) NS).
      apply denote_tc_test_eq_split; [| apply valid_pointer_null].
      repeat apply sepcon_valid_pointer1. apply hci5_p5A_node_valid; exact Hin. }
    entailer!. rewrite Int.eq_false by exact H0.
    destruct (eq_dec na nullval) as [-> | Hn]; [reflexivity |].
    destruct na; try contradiction; [simpl in PNna; subst; contradiction Hn; reflexivity | reflexivity]. }
  { forward. entailer!. rewrite H0. reflexivity. }
  forward_if (hci5_p5A_Q gv L FR R w NS PS T head na KE m (Int.mods (Int.repr b) (Int.repr 3))).
  { (* A's initiation, as the model builds it *)
    assert (Hcm: hci5_p5_c (Int.mods (Int.repr b) (Int.repr 3)) na = true) by (apply hci5_p5A_c_true; exact H0).
    destruct HH as (Hx & Ha & Hxa & Hrep).
    assert (HlA: Zlength (mi_pub (hci5_IA x25519 R)) = 32) by apply Hx.
    assert (HlB: Zlength (mi_pub (hci5_IB x25519 R)) = 32) by apply Hx.
    assert (HlAp: Zlength (mi_priv (hci5_IA x25519 R)) = 32)
      by (apply hci5_p5A_clamp_len; apply H).
    rewrite (hci5_conv_bytes Tsh 32 (l_eraw L)).
    forward_call (l_eraw L, 32, Tsh). Intros er.
    rewrite (hci5_p5A_nd er 32 (l_eraw L)) by tauto.
    rewrite (hci5_p5A_mident_split Tsh (hci5_IB x25519 R) (l_ib L)) by exact HlB. Intros.
    forward_call (Tsh, l_ss1 L, Tsh, l_ia L, hci5_IA x25519 R, Tsh,
                  field_address t_mident [StructField HC._pub] (l_ib L), mi_pub (hci5_IB x25519 R)).
    forward_call (gv, S, w). Intros vr. destruct vr as [sec ns]. cbn [fst snd] in *.
    rewrite hci5_p5A_shim_open. Intros.
    forward. forward.
    forward_call (Tsh, l_ts L, sec, Int64.repr ns).
    gather_SEP (data_at _ tlong _ (gv HC._wg_shim_real_sec)) (data_at _ tlong _ (gv HC._wg_shim_real_nsec))
               (hci5_p5A_shim_rest gv _ _).
    replace_SEP 0 (shim_state4 gv (shim_set_real S sec (Int64.repr ns)) w).
    { rewrite hci5_p5A_shim_open. entailer!. }
    assert (HlT: Zlength (tai64n sec (Int64.repr ns)) = 12) by reflexivity.
    assert (HlS: Zlength (m_precomputed_model x25519 (hci5_IA x25519 R) (mi_pub (hci5_IB x25519 R))) = 32)
      by (unfold m_precomputed_model; destruct (_ && _)%bool; [apply Hx | reflexivity]).
    assert (HlE: Zlength (map Byte.repr er) = 32) by (rewrite Zlength_map; tauto).
    rewrite (hci5_p5A_mident_split Tsh (hci5_IA x25519 R) (l_ia L)) by exact HlA. Intros.
    unfold hci5_consts, wg_consts. Intros.
    forward_call (gv, Tsh, l_mi L, Tsh, field_address t_mident [StructField HC._pub] (l_ia L),
                  mi_pub (hci5_IA x25519 R), field_address t_mident [StructField HC._pub] (l_ib L),
                  mi_pub (hci5_IB x25519 R), l_ss1 L,
                  m_precomputed_model x25519 (hci5_IA x25519 R) (mi_pub (hci5_IB x25519 R)),
                  l_eraw L, map Byte.repr er, l_ts L, tai64n sec (Int64.repr ns)).
    sep_apply (hci5_p5A_mident_join Tsh (hci5_IA x25519 R) (l_ia L) HlA).
    sep_apply (hci5_p5A_mident_join Tsh (hci5_IB x25519 R) (l_ib L) HlB).
    sep_apply (hci5_p5A_hb_out Tsh (m_precomputed_model x25519 (hci5_IA x25519 R) (mi_pub (hci5_IB x25519 R)))
                 (l_ss1 L)). rewrite HlS.
    sep_apply (hci5_p5A_hb_out Tsh (map Byte.repr er) (l_eraw L)). rewrite HlE.
    sep_apply (hci5_p5A_ts_in (tai64n sec (Int64.repr ns)) (l_ts L) HlT).
    forward_if (hci5_p5A_Q1 gv L FR R w NS PS T head na KE m (Int.mods (Int.repr b) (Int.repr 3))).
    { destruct (m_create_initiation_model x25519 aead_enc _ _ _ _ _) as [[[[[[E encs] enct] ep] ck] h] |] eqn:Hci;
        [| contradiction].
      destruct (hci5_p5A_cinit_len _ _ _ _ _ _ _ _ _ _ _ Hx Ha Hci) as (HlE' & Hls & Hlt).
      rewrite ?HlA, ?Hx in Hls. rewrite HlT in Hlt. cbn in Hls, Hlt.
      unfold init_rep. Intros. destruct M as [ty se eph0 encs0 enct0 mac1 mac2].
        destruct H1 as (Hl1 & Hl2 & Hl3 & Hl4 & Hl5); cbn [im_eph im_encs im_enct im_mac1 im_mac2] in *.
        rewrite (hci5_p5A_init_split Ews ty se eph0 encs0 enct0 mac1 mac2 m Hl1 Hl2 Hl3).
        rewrite (hci5_p5A_minit_split Tsh E encs enct ep ck h (l_mi L) HlE' Hls Hlt). Intros.
        assert_PROP (field_compatible t_init [] m /\ field_compatible t_minit [] (l_mi L)) as Hf12.
        { go_lower. saturate_local. apply prop_right. split.
          - match goal with Hc: field_compatible t_init (DOT HC._macs) m |- _ =>
              apply field_compatible_cons in Hc; exact (proj2 Hc) end.
          - match goal with Hc: field_compatible t_minit (DOT HC._st) (l_mi L) |- _ =>
              apply field_compatible_cons in Hc; exact (proj2 Hc) end. }
        destruct Hf12 as [Hf1 Hf2].
        forward.
        sep_apply (hci5_p5A_hb_out Ews eph0 (field_address t_init [StructField HC._unencrypted_ephemeral] m)).
        rewrite Hl1.
        forward_call (Ews, field_address t_init [StructField HC._unencrypted_ephemeral] m, Tsh,
                      field_address t_minit [StructField HC._ephemeral] (l_mi L), E).
        { rewrite HlE'. entailer!.
          all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
        { rewrite HlE'. cancel. }
        sep_apply (hci5_p5A_hb_out Ews encs0 (field_address t_init [StructField HC._encrypted_static] m)).
        rewrite Hl2.
        forward_call (Ews, field_address t_init [StructField HC._encrypted_static] m, Tsh,
                      field_address t_minit [StructField HC._enc_static] (l_mi L), encs).
        { rewrite Hls. entailer!.
          all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
        { rewrite Hls. cancel. }
        sep_apply (hci5_p5A_hb_out Ews enct0 (field_address t_init [StructField HC._encrypted_timestamp] m)).
        rewrite Hl3.
        forward_call (Ews, field_address t_init [StructField HC._encrypted_timestamp] m, Tsh,
                      field_address t_minit [StructField HC._enc_timestamp] (l_mi L), enct).
        { rewrite Hlt. entailer!.
          all: simpl; unfold field_address; rewrite !if_true by auto with field_compatible; reflexivity. }
        { rewrite Hlt. cancel. }
        sep_apply (hci5_p5A_minit_join Tsh E encs enct ep ck h (l_mi L) HlE' Hls Hlt).
        sep_apply (hci5_p5A_init_join Ews (Int.repr 1) se E encs enct mac1 mac2 m HlE' Hls Hlt Hl4 Hl5).
        unfold hci5_p5A_Q1. Exists (mkIM (Int.repr 1) se E encs enct mac1 mac2) (shim_set_real S sec (Int64.repr ns)).
        unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
        entailer!. unfold im_ok; simpl; auto. }
    { destruct (m_create_initiation_model x25519 aead_enc _ _ _ _ _) as [[[[[[E encs] enct] ep] ck] h] |] eqn:Hci;
        [discriminate |].
      forward. unfold hci5_p5A_Q1. Exists M (shim_set_real S sec (Int64.repr ns)).
      unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
      entailer!. }
    unfold hci5_p5A_Q1. Intros M2 S2. unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
    forward_if (hci5_p5A_Q gv L FR R w NS PS T head na KE m (Int.mods (Int.repr b) (Int.repr 3))).
    { forward_call tt. Intros kk.
      forward.
      forward_call tt. Intros dd.
      forward.
      { entailer!. split; [| intros [_ Hc]; discriminate]. unfold Int.mods.
        rewrite (Int.signed_repr dd) by rep_lia. rewrite (Int.signed_repr 255) by rep_lia.
        pose proof (Z.rem_bound_pos dd 255 ltac:(lia) ltac:(lia)). rewrite Int.signed_repr by rep_lia. rep_lia. }
      assert (Hk: Int64.modu (Int64.repr kk) (Int64.repr (Int.signed (Int.repr 116))) = Int64.repr (kk mod 116)).
      { change (Int.signed (Int.repr 116)) with 116.
        unfold Int64.modu. rewrite !Int64.unsigned_repr by rep_lia. reflexivity. }
      rewrite Hk.
      assert (Hkr: 0 <= kk mod 116 < 116) by (apply Z.mod_pos_bound; lia).
      set (dv := Int.zero_ext 8 (Int.zero_ext 8 (Int.add (Int.repr 1) (Int.mods (Int.repr dd) (Int.repr 255))))).
      unfold init_rep. Intros. rewrite hci5_p5A_init_W.
      destruct M2 as [ty se eph mac0 enct mac1 mac2].
      destruct H7 as (Hl1 & Hl2 & Hl3 & Hl4 & Hl5); cbn [im_eph im_encs im_enct im_mac1 im_mac2] in *.
      forward_if.
      { forward. forward.
        unfold hci5_p5A_Q. Exists (mkIM ty (Int.xor se dv) eph mac0 enct mac1 mac2) S2.
        unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
        unfold init_rep. rewrite hci5_p5A_init_W. entailer!. unfold im_ok; simpl; repeat split; auto. }
      rewrite !Int64.unsigned_repr in H7 by rep_lia.
      forward_if.
      { rewrite !Int64.unsigned_repr in H11 by rep_lia.
        unfold init_val. cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        forward.
        { entailer!. try rewrite hci5_p5A_Znth_bytes by lia. exact (tc_val_Vubyte _). }
        rewrite hci5_p5A_Znth_bytes by lia.
        forward.
        rewrite hci5_p5A_upd_bytes by lia.
        unfold hci5_p5A_Q.
        Exists (mkIM ty se (upd_Znth (kk mod 116 - 8) eph (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth (kk mod 116 - 8) eph))) dv)))) mac0 enct mac1 mac2) S2.
        unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
        unfold init_rep. rewrite hci5_p5A_init_W. unfold init_val.
        cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        entailer!. unfold im_ok; simpl; rewrite ?upd_Znth_Zlength by lia; repeat split; auto. }
      rewrite !Int64.unsigned_repr in H11 by rep_lia.
      forward_if.
      { rewrite !Int64.unsigned_repr in H12 by rep_lia.
        unfold init_val. cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        forward.
        { entailer!. try rewrite hci5_p5A_Znth_bytes by lia. exact (tc_val_Vubyte _). }
        rewrite hci5_p5A_Znth_bytes by lia.
        forward.
        rewrite hci5_p5A_upd_bytes by lia.
        unfold hci5_p5A_Q.
        Exists (mkIM ty se eph (upd_Znth (kk mod 116 - 40) mac0 (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth (kk mod 116 - 40) mac0))) dv)))) enct mac1 mac2) S2.
        unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
        unfold init_rep. rewrite hci5_p5A_init_W. unfold init_val.
        cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        entailer!. unfold im_ok; simpl; rewrite ?upd_Znth_Zlength by lia; repeat split; auto. }
      { rewrite !Int64.unsigned_repr in H12 by rep_lia.
        unfold init_val. cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        forward.
        { entailer!. try rewrite hci5_p5A_Znth_bytes by lia. exact (tc_val_Vubyte _). }
        rewrite hci5_p5A_Znth_bytes by lia.
        forward.
        rewrite hci5_p5A_upd_bytes by lia.
        unfold hci5_p5A_Q.
        Exists (mkIM ty se eph mac0 (upd_Znth (kk mod 116 - 88) enct (Byte.repr (Int.unsigned (Int.xor (Int.repr (Byte.unsigned (Znth (kk mod 116 - 88) enct))) dv)))) mac1 mac2) S2.
        unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
        unfold init_rep. rewrite hci5_p5A_init_W. unfold init_val.
        cbn [im_type im_sender im_eph im_encs im_enct im_mac1 im_mac2].
        entailer!. unfold im_ok; simpl; rewrite ?upd_Znth_Zlength by lia; repeat split; auto. }
    }
    { forward. unfold hci5_p5A_Q. Exists M2 S2. unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
      entailer!. }
    }
  { assert (Hcm: hci5_p5_c (Int.mods (Int.repr b) (Int.repr 3)) na = false) by (apply hci5_p5A_c_false; exact H0).
    forward. unfold hci5_p5A_Q. Exists M S. unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
    entailer!. }
  unfold hci5_p5A_Q. Intros M' S'.
  unfold hci5_p5_Q17. Exists R S' w NS PS T head na KE m M' (Int.mods (Int.repr b) (Int.repr 3)).
  unfold hci5_lvars, hci5_snaps0, hci5_scr, hci5_p5_scr, hci5_world, hci5_globs, hci5_consts, wg_consts; cbn [app]. try rewrite Hcm.
  entailer!. unfold hci5_inv; tauto.
Qed.

End P5A.
