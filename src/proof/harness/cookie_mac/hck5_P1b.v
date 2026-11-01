(* law cookie_mac: main's phase P1b, statements 20..27 of hck5_cut.v:
   NEW (v2): hs_randomize(&p.handshake), p.is_dead, p.last_sent_handshake.counter, p.refcount.refcount, maybe wg_index_hashtable_insert(&ita, &p.handshake.entry), kes = kents_add(&ita, NULL, &p, 1), kents_snap(kes), head0 = ita.head.
*)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_mac.hck5_cut.
Require Import WgNoise.proof.harness.cookie_mac.hck5_spec.
Require Import WgNoise.proof.harness.cookie_mac.hck5_defs.
Require Import WgNoise.proof.harness.cookie_mac.hck5_conv.
Require WgNoise.harness.x_cookie_mac.code.

#[local] Existing Instance W_cookie_mac.
Local Open Scope Z_scope.

#[local] Instance hck5_p1b_CCE : change_composite_env Noise.CS W_cookie_mac.
Proof. make_cs_preserve Noise.CS W_cookie_mac. Defined.

Lemma hck5_p1b_lsh_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong v) p =
  @field_at Noise.CS sh t_peer [StructField I._counter; StructField I._last_sent_handshake] (Vlong v) p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hck5_p1b_refs_nest sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at Noise.CS sh t_peer [StructField I._refcount; StructField I._refcount] (Vint v) p.
Proof. unfold_field_at 1%nat. reflexivity. Qed.

Lemma hck5_p1b_dead_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._is_dead] v p =
  @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._is_dead] v p.
Proof.
  change (Tstruct HK._wg_peer noattr) with t_peer. change HK._is_dead with I._is_dead.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_cookie_mac _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

Lemma hck5_p1b_lsh_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._last_sent_handshake] (Vlong v) p =
  @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._counter; StructField HK._last_sent_handshake] (Vlong v) p.
Proof.
  rewrite hck5_p1b_lsh_nest.
  change (Tstruct HK._wg_peer noattr) with t_peer. change HK._counter with I._counter.
  change HK._last_sent_handshake with I._last_sent_handshake.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_cookie_mac _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

Lemma hck5_p1b_refs_conv sh p v :
  @field_at Noise.CS sh t_peer [StructField I._refcount] (Vint v) p =
  @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint v) p.
Proof.
  rewrite hck5_p1b_refs_nest.
  change (Tstruct HK._wg_peer noattr) with t_peer. change HK._refcount with I._refcount.
  apply equal_f. apply (@field_at_change_composite Noise.CS W_cookie_mac _ sh t_peer); [apply JMeq_refl | reflexivity].
Qed.

Lemma hck5_p1b_fold sh p P C :
  (hck5_prest sh p P * cookie_rep sh (cookie_addr p) C)%logic = peer_rep sh p (p_set_cookie P C).
Proof.
  unfold hck5_prest, peer_rep. destruct P; simpl. apply pred_ext; Intros; entailer!.
Qed.

Lemma hck5_p1b_split sh p P :
  peer_rep sh p P = (hck5_prest sh p P * cookie_rep sh (cookie_addr p) (p_cookie P))%logic.
Proof.
  unfold hck5_prest, peer_rep. apply pred_ext; Intros; entailer!.
Qed.

(* p with ANY dead flag, last sent handshake and reference count *)
Definition hck5_p1b_set3 (P: peer) (dead: bool) (lsh: int64) (r: int) : peer :=
  mkPeer (p_device P) dead (p_cur P) (p_prev P) (p_next P) (p_hs P) lsh (p_cookie P) r (p_id P) (p_pknext P).

(* hck5_prest without the three fields the harness stores *)
Definition hck5_p1b_prest3 (sh: share) (p: val) (P: peer) : mpred :=
  !! @field_compatible Noise.CS t_peer [] p &&
  (@field_at Noise.CS sh t_peer [StructField I._device] (p_device P) p *
   kps_rep sh (kps_addr p) (p_cur P) (p_prev P) (p_next P) *
   hs_rep sh (hs_addr p) (p_hs P) *
   @field_at Noise.CS sh t_peer [StructField I._internal_id] (Vlong (p_id P)) p *
   @field_at Noise.CS sh t_peer [StructField I._pubkey_next] (p_pknext P) p *
   spacer sh 9 16 p * spacer sh 476 480 p)%logic.

Lemma hck5_p1b_open sh p P :
  hck5_prest sh p P |--
  (hck5_p1b_prest3 sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._is_dead] (Val.of_bool (p_dead P)) p *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._counter; StructField HK._last_sent_handshake] (Vlong (p_lsh P)) p *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint (p_refs P)) p)%logic.
Proof.
  rewrite <- hck5_p1b_dead_conv, <- hck5_p1b_lsh_conv, <- hck5_p1b_refs_conv.
  unfold hck5_prest, hck5_p1b_prest3. Intros. entailer!.
Qed.

Lemma hck5_p1b_close sh p P dead lsh r :
  (hck5_p1b_prest3 sh p P *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._is_dead] (Val.of_bool dead) p *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._counter; StructField HK._last_sent_handshake] (Vlong lsh) p *
   @field_at W_cookie_mac sh (Tstruct HK._wg_peer noattr) [StructField HK._refcount; StructField HK._refcount] (Vint r) p)%logic
  |-- hck5_prest sh p (hck5_p1b_set3 P dead lsh r).
Proof.
  rewrite <- hck5_p1b_dead_conv, <- hck5_p1b_lsh_conv, <- hck5_p1b_refs_conv.
  unfold hck5_prest, hck5_p1b_prest3, hck5_p1b_set3. simpl. Intros. entailer!.
Qed.

(* p's handshake entry joins the empty pool of A's table *)
Lemma hck5_p1b_entry_fold sht tab sh a E :
  writable_share sh ->
  itable sht tab (mkT [] []) * entry_out sh a E |-- itable sht tab (mkT [(a, sh, E)] []).
Proof.
  intros Hw. unfold itable, itable_wf. simpl. Intros. unfold entry_out.
  unfold vin. simpl. entailer!.
  split; [intros x [] | constructor; [intros [] | constructor]].
Qed.

(* the pool after the maybe-insert: p's handshake entry only *)
Definition hck5_p1b_T0 (p: val) (T: tstate) : Prop :=
  exists i, t_D T = [(hs_addr p, Tsh, mkEntry p IDX_HANDSHAKE i)].

Lemma hck5_p1b_T0_insert p idx :
  hck5_p1b_T0 p (t_insert (mkT [(hs_addr p, Tsh, mkEntry p IDX_HANDSHAKE Int.zero)] []) (hs_addr p) idx).
Proof.
  exists idx. unfold t_insert, t_set_index, t_entry, t_upd. simpl.
  destruct (EqDec_val (hs_addr p) (hs_addr p)) as [_|n]; [| congruence]. simpl.
  destruct (EqDec_val (hs_addr p) (hs_addr p)) as [_|n]; [| congruence]. reflexivity.
Qed.

(* ---- kents_add / kents_snap (port of create_any's hca5_PD helpers) ---- *)

(* the peer p after kents_add's fills (every kent owned by p) *)
Fixpoint hck5_p1b_fill (P: peer) (KD: list kdraw) : peer :=
  match KD with [] => P | d :: KD' => fill_slot (hck5_p1b_fill P KD') (kd_addr d) (kd_slot d) end.

Lemma hck5_p1b_owners p sh P KD :
  kents_draws_ok [(p, sh, P)] KD -> Forall (fun d => kd_owner d = p) KD.
Proof.
  intros [Hf _]. eapply Forall_impl; [| exact Hf].
  intros d [Hin _]. simpl in Hin. destruct Hin as [-> | []]. reflexivity.
Qed.

Lemma hck5_p1b_PS p sh P KD :
  Forall (fun d => kd_owner d = p) KD -> kents_PS true [(p, sh, P)] KD = [(p, sh, hck5_p1b_fill P KD)].
Proof.
  induction KD as [| d KD IH]; intros Ho; [reflexivity |].
  inversion Ho as [| ? ? Hd Ho']; subst. simpl. rewrite IH by exact Ho'.
  unfold fill_peers. simpl. destruct (EqDec_val (kd_owner d) (kd_owner d)); [reflexivity | congruence].
Qed.

Lemma hck5_p1b_fill_fields P KD :
  p_device (hck5_p1b_fill P KD) = p_device P /\ p_hs (hck5_p1b_fill P KD) = p_hs P /\
  p_pknext (hck5_p1b_fill P KD) = p_pknext P /\ p_cookie (hck5_p1b_fill P KD) = p_cookie P.
Proof.
  induction KD as [| d KD IH]; [auto |]. simpl.
  destruct IH as (H1 & H2 & H3 & H4).
  unfold fill_slot; repeat first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)];
    unfold p_set_slots; simpl; auto.
Qed.

Lemma hck5_p1b_slots_step P ks k c :
  Forall (fun v => v = nullval \/ In v ks) [p_cur P; p_prev P; p_next P] ->
  Forall (fun v => v = nullval \/ In v (k :: ks)) [p_cur (fill_slot P k c); p_prev (fill_slot P k c); p_next (fill_slot P k c)].
Proof.
  intros Hsl.
  assert (Hsl': Forall (fun v => v = nullval \/ In v (k :: ks)) [p_cur P; p_prev P; p_next P]).
  { eapply Forall_impl; [| exact Hsl]. intros v [? | ?]; [left | right; right]; auto. }
  inversion Hsl' as [| ? ? Hc Hsl1]; subst; inversion Hsl1 as [| ? ? Hp Hsl2]; subst;
    inversion Hsl2 as [| ? ? Hn _]; subst.
  assert (Hk: k = nullval \/ In k (k :: ks)) by (right; left; reflexivity).
  unfold fill_slot; repeat first [destruct (Z.eq_dec _ _) | destruct (eq_dec _ _)];
    unfold p_set_slots; simpl; repeat (apply Forall_cons; [assumption |]); apply Forall_nil.
Qed.

Lemma hck5_p1b_slots P KD :
  p_cur P = nullval -> p_prev P = nullval -> p_next P = nullval ->
  Forall (fun v => v = nullval \/ In v (map kd_addr KD))
    [p_cur (hck5_p1b_fill P KD); p_prev (hck5_p1b_fill P KD); p_next (hck5_p1b_fill P KD)].
Proof.
  intros Hc Hp Hn. induction KD as [| d KD IH].
  - simpl. rewrite Hc, Hp, Hn. repeat constructor.
  - simpl. apply hck5_p1b_slots_step, IH.
Qed.

Definition hck5_p1b_kpool (p: val) (d: kdraw) : val * share * entry :=
  (kd_addr d, Ews, mkEntry p IDX_KEYPAIR (kd_idx d)).

Lemma hck5_p1b_ins_eq T a sh E idx :
  t_insert (t_add T a sh E) a idx =
  mkT ((a, sh, mkEntry (e_peer E) (e_type E) idx) :: t_D T) (a :: vremove a (t_L T)).
Proof.
  unfold t_insert, t_set_index, t_entry, t_add, t_upd. simpl.
  destruct (EqDec_val a a); [| congruence]. simpl.
  destruct (EqDec_val a a); [| congruence]. reflexivity.
Qed.

Lemma hck5_p1b_TD p T KD :
  Forall (fun d => kd_owner d = p) KD -> t_D (kents_T T KD) = map (hck5_p1b_kpool p) KD ++ t_D T.
Proof.
  induction KD as [| d KD IH]; intros Ho; [reflexivity |].
  inversion Ho as [| ? ? Hd Ho']; subst. simpl kents_T. rewrite hck5_p1b_ins_eq. simpl.
  rewrite IH by exact Ho'. reflexivity.
Qed.

Lemma hck5_p1b_saddrs p KD : saddrs (map (hck5_p1b_kpool p) KD) = map kd_addr KD.
Proof. induction KD as [| d KD IH]; simpl; [reflexivity | rewrite <- IH; reflexivity]. Qed.

(* kents_snap's precondition *)
Lemma hck5_p1b_entry p T KD a :
  Forall (fun d => kd_owner d = p) KD -> In a (map kd_addr KD) ->
  In a (saddrs (t_D (kents_T T KD))) /\ e_peer (t_entry_d (kents_T T KD) a) = p.
Proof.
  intros Ho Hin. unfold t_entry_d, t_entry. rewrite (hck5_p1b_TD p T KD Ho). clear Ho.
  split.
  - unfold saddrs. rewrite map_app. apply in_or_app. left.
    change (map (fun '(x, _, _) => x) (map (hck5_p1b_kpool p) KD)) with (saddrs (map (hck5_p1b_kpool p) KD)).
    rewrite hck5_p1b_saddrs. exact Hin.
  - induction KD as [| d KD IH]; [destruct Hin |]. simpl.
    destruct (EqDec_val (kd_addr d) a); [reflexivity |].
    apply IH. destruct Hin as [Heq | Hin]; [congruence | exact Hin].
Qed.

Lemma hck5_p1b_kents_ptr l KE : kents_rep W_cookie_mac l KE |-- !! Forall (fun e => isptr (ke_addr e)) KE.
Proof.
  revert l; induction KE as [| e KE IH]; intros l; simpl.
  - entailer!.
  - Intros nx. unfold kent_cell. Intros. sep_apply (IH nx). Intros. apply prop_right.
    constructor; auto. exact (@field_compatible_isptr CKS _ _ _ H0).
Qed.

(* the pool facts of hck5_aok *)
Lemma hck5_p1b_pool p T KD :
  hck5_p1b_T0 p T -> Forall (fun d => kd_owner d = p) KD ->
  let T' := kents_T T KD in let KE := map (kent_snapped T') (map kd_kent KD) in
  saddrs (t_D T') = map ke_addr KE ++ [hs_addr p] /\
  map (fun x => snd (fst x)) (t_D T') = map (fun _ => Ews) KE ++ [Tsh] /\
  Forall (fun x => e_peer (snd x) = p) (t_D T') /\
  Forall (fun e => kent_snapped T' e = e) KE.
Proof.
  intros [i Hi] Ho. cbv zeta. rewrite (hck5_p1b_TD p T KD Ho), Hi.
  repeat split.
  - unfold saddrs. rewrite map_app. f_equal.
    change (map (fun '(x, _, _) => x) (map (hck5_p1b_kpool p) KD)) with (saddrs (map (hck5_p1b_kpool p) KD)).
    rewrite hck5_p1b_saddrs. rewrite !map_map. reflexivity.
  - rewrite map_app. f_equal. rewrite !map_map. reflexivity.
  - apply Forall_app. split; [| repeat constructor].
    apply Forall_map. apply Forall_forall. intros; reflexivity.
  - apply Forall_map. apply Forall_forall. intros; reflexivity.
Qed.

Lemma hck5_p1b_itab_conv sh (v: val) p : @data_at Noise.CS sh t_itab v p = @data_at W_cookie_mac sh t_itab v p.
Proof.
  apply equal_f. apply (@data_at_change_composite Noise.CS W_cookie_mac _ sh t_itab); [apply JMeq_refl | reflexivity].
Qed.

Lemma hck5_p1b_hd T KE p :
  incl (t_L T) (saddrs (t_D T)) -> saddrs (t_D T) = map ke_addr KE ++ [hs_addr p] ->
  Forall (fun e => isptr (ke_addr e)) KE -> isptr p -> is_pointer_or_null (hd nullval (t_L T)).
Proof.
  intros Hi Hs Hk Hp. destruct (t_L T) as [| a l] eqn:E; simpl; [simpl; auto |].
  assert (Ha: In a (saddrs (t_D T))) by (apply Hi; left; reflexivity).
  rewrite Hs in Ha. apply in_app_or in Ha. destruct Ha as [Ha | [<- | []]].
  - apply in_map_iff in Ha. destruct Ha as (e & <- & He). rewrite Forall_forall in Hk.
    specialize (Hk e He). destruct (ke_addr e); try contradiction; exact I.
  - unfold hs_addr. destruct p; try contradiction; exact I.
Qed.

Section P1b.
Variable x25519: list byte -> list byte -> list byte.
Variable aead_enc: list byte -> Z -> list byte -> list byte -> list byte.
Variable aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte).
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

Lemma hck5_P1b_ok {Espec: OracleKind} gv L FR :
  hck5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  semax (hck5_Delta x25519 aead_enc aead_dec xaead_enc xaead_dec) (hck5_S1 x25519 gv L FR) hck5_P1b
    (overridePost (hck5_S1b x25519 gv L FR) (hck5_R gv)).
Proof.
  intros HH. unfold hck5_S1, hck5_S1b, hck5_Delta, hck5_R, hck5_P1b. simplify_func_tycontext. abbreviate_semax.
  Intros R S.
  unfold hck5_aside1, hck5_lvars, hck5_scr, hck5_bside, hck5_bufs, hck5_globs, hck5_snaps0; simpl app.
  gather_SEP 3 13. rewrite hck5_p1b_fold.
  (* hs_randomize(&p.handshake) *)
  forward_call (Tsh, l_p L, p_set_cookie (hck5_P0 x25519 R L) (hck5_C0 R), false).
  Intros vret. destruct vret as [[[[[[[st lic] eph] reph] hash] ck] ts] ri]; simpl fst in *; simpl snd in *.
  (* p.is_dead, p.last_sent_handshake.counter, p.refcount.refcount *)
  forward_call tt. Intros d8.
  match goal with |- context [peer_rep Tsh (l_p L) ?P] => set (P1 := P) end.
  rewrite hck5_p1b_split. sep_apply (hck5_p1b_open Tsh (l_p L) P1). Intros.
  forward.
  forward_call tt. Intros u64.
  forward.
  forward_call tt. Intros r.
  forward.
  set (dead := negb (Int.eq (Int.and (Int.repr d8) (Int.repr 1)) Int.zero)).
  replace (Vint (if Int.eq (Int.and (Int.repr d8) (Int.repr 1)) Int.zero then Int.zero else Int.one))
    with (Val.of_bool dead) by (unfold dead; destruct (Int.eq _ _); reflexivity).
  sep_apply (hck5_p1b_close Tsh (l_p L) P1 dead u64 r).
  set (P2 := hck5_p1b_set3 P1 dead u64 r).
  gather_SEP (hck5_prest _ _ _) (cookie_rep _ _ _). rewrite hck5_p1b_fold.
  forward_call tt. Intros b8.
  (* if (nondet_u8() & 1) wg_index_hashtable_insert(&ita, &p.handshake.entry) *)
  sep_apply (hck5_p1b_entry_fold Tsh (l_ita L) Tsh (hs_addr (l_p L)) (hck5_E L) writable_share_top).
  set (P3 := p_set_cookie P2 (p_cookie P1)).
  forward_if (EX T: tstate, EX S1: shim,
    PROPx [hck5_p1b_T0 (l_p L) T]
    (LOCALx ([temp HK._corrupted (Vint Int.zero);
              temp HK._honest_peer (Vint (if r_honest R then Int.one else Int.zero))] ++ hck5_lvars gv L)
    (SEPx ([peer_rep Tsh (l_p L) P3; device_rep Tsh (l_wa L) (hck5_DA x25519 R L); itable Tsh (l_ita L) T;
            ptable Tsh (l_pta L) (l_p L)] ++ hck5_bside x25519 R L ++ hck5_bufs x25519 R L ++
           [checker_rep Tsh (cc_addr (l_wb L)) (hck5_CC1 x25519 R L); @data_at_ Cookie.CS Tsh t_skb (l_skb L)] ++
           hck5_scr L ++ hck5_snaps0 L ++ hck5_globs gv S1 FR)))).
  - forward_call (gv, S, hck5_w0, Tsh, l_ita L, mkT [(hs_addr (l_p L), Tsh, hck5_E L)] [], hs_addr (l_p L),
                  @None (share * entry)).
    { change (raw_rep (hs_addr (l_p L)) None) with emp. rewrite emp_sepcon. cancel. }
    { simpl; auto. }
    change (raw_add _ (hs_addr (l_p L)) None) with (mkT [(hs_addr (l_p L), Tsh, hck5_E L)] []). Intros idx.
    Exists (t_insert (mkT [(hs_addr (l_p L), Tsh, hck5_E L)] []) (hs_addr (l_p L)) idx) (shim_u32 S idx).
    unfold hck5_lvars, hck5_scr, hck5_bside, hck5_bufs, hck5_globs, hck5_snaps0; simpl app.
    entailer!. apply hck5_p1b_T0_insert.
  - forward.
    Exists (mkT [(hs_addr (l_p L), Tsh, hck5_E L)] []) S.
    unfold hck5_lvars, hck5_scr, hck5_bside, hck5_bufs, hck5_globs, hck5_snaps0; simpl app.
    entailer!. exists Int.zero. reflexivity.
  - Intros T S1.
    unfold hck5_lvars, hck5_scr, hck5_bside, hck5_bufs, hck5_globs, hck5_snaps0; simpl app.
    match goal with Hx: hck5_p1b_T0 _ _ |- _ => rename Hx into HT0 end.
    (* kes = kents_add(&ita, NULL, &p, 1) *)
    assert_PROP (isptr (l_p L)) as Hpp by entailer!.
    assert (Hpn: l_p L <> nullval) by (destruct (l_p L); try contradiction; discriminate).
    replace_SEP 0 (peers_rep [(l_p L, Tsh, P3)] * hnodes_rep4 W_cookie_mac nullval [])%logic.
    { entailer!. unfold peers_rep, hnodes_rep4; simpl. entailer!. }
    forward_call (gv, Tsh, l_ita L, T, nullval, @nil hnode4, l_p L, [(l_p L, Tsh, P3)], Int.one, S1, hck5_w0).
    { cancel. }
    { split; [apply Forall_cons; [apply writable_share_top | apply Forall_nil] |].
      split.
      - unfold kents_owners_ok. rewrite if_true by auto. split; auto. simpl. rewrite if_false; auto.
      - (* common4 v4.1: the owner's slots are NULL *)
        apply Forall_cons; [| apply Forall_nil]; simpl; repeat apply Forall_cons; try apply Forall_nil;
          left; reflexivity. }
    Intros KD.
    match goal with Hx: kents_draws_ok _ _ |- _ => rename Hx into Hdr end.
    pose proof (hck5_p1b_owners _ _ _ _ Hdr) as Ho.
    change (negb (Int.eq Int.one Int.zero)) with true.
    rewrite (hck5_p1b_PS _ _ _ _ Ho).
    change (peers_rep [(l_p L, Tsh, hck5_p1b_fill P3 KD)]) with (peer_rep Tsh (l_p L) (hck5_p1b_fill P3 KD) * emp)%logic.
    change (hnodes_rep4 W_cookie_mac nullval []) with (!!(nullval = nullval) && emp)%logic.
    (* kents_snap(kes) *)
    forward_call (kents_head KD, map kd_kent KD, Tsh, l_ita L, kents_T T KD).
    { rewrite Forall_forall. intros e He'. apply in_map_iff in He'. destruct He' as (d & <- & Hd).
      destruct (hck5_p1b_entry (l_p L) T KD (kd_addr d) Ho (in_map kd_addr _ _ Hd)) as [Hi He].
      cbn [ke_addr kd_kent]. split; [exact Hi | rewrite He; destruct (l_p L); try contradiction; discriminate]. }
    rewrite sepcon_emp. Intros.
    (* head0 = ita.head *)
    assert_PROP (Forall (fun e => isptr (ke_addr e)) (map (kent_snapped (kents_T T KD)) (map kd_kent KD))) as Hkp
      by (sep_apply (hck5_p1b_kents_ptr (kents_head KD) (map (kent_snapped (kents_T T KD)) (map kd_kent KD)));
          entailer!).
    assert_PROP (@field_compatible Noise.CS t_peer [] (l_p L)) as Hfc by (unfold peer_rep; entailer!).
    destruct (hck5_p1b_pool (l_p L) T KD HT0 Ho) as (Q1 & Q2 & Q3 & Q4).
    unfold itable at 1. Intros.
    match goal with Hx: itable_wf _ |- _ => pose proof Hx as Hwf end.
    assert (Hhd: is_pointer_or_null (hd nullval (t_L (kents_T T KD)))).
    { destruct Hwf as (_ & Hincl & _). eapply hck5_p1b_hd; eauto. }
    rewrite hck5_p1b_itab_conv.
    forward.
    rewrite <- hck5_p1b_itab_conv.
    gather_SEP 1 2. replace_SEP 0 (itable Tsh (l_ita L) (kents_T T KD)).
    { unfold itable. entailer!. }
    rewrite hck5_p1b_split.
    destruct (hck5_p1b_fill_fields P3 KD) as (Fd & Fh & Fp & Fc).
    rewrite Fc. change (p_cookie P3) with (hck5_C0 R).
    assert (Haok: hck5_aok L (mkA5 (kents_T T KD) (hck5_p1b_fill P3 KD)
                                (map (kent_snapped (kents_T T KD)) (map kd_kent KD)) (kents_head KD)
                                (hd nullval (t_L (kents_T T KD))))).
    { unfold hck5_aok; cbn [a_T a_P a_KE a_kes a_head0].
      rewrite Fd, Fh, Fp.
      refine (conj Hfc (conj eq_refl (conj eq_refl (conj eq_refl (conj _ (conj Hkp (conj Q1 (conj Q2 (conj Q3 (conj Q4 eq_refl)))))))))).
      replace (map ke_addr (map (kent_snapped (kents_T T KD)) (map kd_kent KD))) with (map kd_addr KD)
        by (rewrite !map_map; reflexivity).
      apply hck5_p1b_slots; reflexivity. }
    Exists R (kents_S S1 KD) (mkA5 (kents_T T KD) (hck5_p1b_fill P3 KD)
                                (map (kent_snapped (kents_T T KD)) (map kd_kent KD)) (kents_head KD)
                                (hd nullval (t_L (kents_T T KD)))).
    unfold hck5_A, hck5_lvars, hck5_scr, hck5_bside, hck5_bufs, hck5_globs, hck5_snaps0; cbn [a_T a_P a_KE a_kes a_head0]; simpl app.
    entailer!.
Qed.

End P1b.
