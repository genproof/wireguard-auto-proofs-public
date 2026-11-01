(* law cookie_reply, phase P11: the cut into three segments, the two intermediate states, the harness's walk
   of A's table as a function and the pure agreement of the harness's target with the kernel's model.
   Port of v1's hcy4_p11_defs.v + hcy4_p11_agree.v.
   - A = statements 66..67: target = NULL; for (e = ita.head; e != NULL && e->index != reply->receiver_index;
         e = e->next);                                             S10 -> hcy5_p11_TA
   - B = statement 68: if (e != NULL && (e->type & 3)) for (cn = cns; cn; cn = cn->next)
         if (cn->n->p == e->peer && target == NULL) target = cn;   hcy5_p11_TA -> hcy5_p11_TB
   - C = statement 69: if (target != NULL) { decrypt; target = NULL or the CHECK of the accepted peer }
                                                                   hcy5_p11_TB -> S11
   TA = S10 with target = NULL and e = the first entry of the table with the reply's receiver index (or NULL);
   TB = S10 with target = hcy5_p11_t0 (the cnode of the peer of the entry t_lookup finds, or NULL). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol.prot_rep_lemmas3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.common4.hc4_prog.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_cut.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_spec.
Require Import WgNoise.proof.harness.cookie_reply.hcy5_defs.
Require WgNoise.harness.x_cookie_reply.code.

#[local] Existing Instance W_cookie_reply.
Local Open Scope logic.

Definition hcy5_p11_sA := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 66 2)) in exact x).
Definition hcy5_p11_sB := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 68 1)) in exact x).
Definition hcy5_p11_sC := ltac:(let x := eval cbv beta iota delta [hcy5_l hcy5_seql firstn skipn hcy5_stmts] in (hcy5_seql (hcy5_l 69 1)) in exact x).

Lemma hcy5_p11_eq : hcy5_P11 = hcy5_seqs (hcy5_l 66 2) (Ssequence hcy5_p11_sB hcy5_p11_sC).
Proof. reflexivity. Qed.
Lemma hcy5_p11_eqA : hcy5_p11_sA = hcy5_seql (hcy5_l 66 2).
Proof. reflexivity. Qed.

(* the harness's walk of A's table: the first entry of the list with that index, or NULL *)
Definition hcy5_p11_ewalk (T: tstate) (idx: int) : val :=
  match t_find_index T (t_L T) idx with Some (a, _) => a | None => nullval end.

(* the harness's target before the decryption: the cnode of the peer of the entry the kernel's lookup finds
   (index idx, type handshake or keypair), or NULL *)
Definition hcy5_p11_t0 (NS: list hnode4) (CL: list (val * val * option cookie)) (T: tstate) (idx: int) : val :=
  match t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) idx with
  | Some (_, E) => hcy5_cfind NS CL (e_peer E)
  | None => nullval
  end.

Section States.
Variable x25519: list byte -> list byte -> list byte.
Variable xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte.
Variable xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte).

(* after A: S10 with target = NULL and e = the walk's result *)
Definition hcy5_p11_TA (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  EX now2: int64,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np;
         0 <= Int64.unsigned now2 < 2 ^ 62]
  (LOCALx ([temp HY._target nullval; temp HY._e (hcy5_p11_ewalk T (cm_receiver CM'));
            temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T)); temp HY._now (Vlong now2)] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S hcy5_w0) (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

(* after B: S10 with target = hcy5_p11_t0 (e is dead) *)
Definition hcy5_p11_TB (gv: globals) (L: hcy5_loc) (FR: mpred) : environ -> mpred :=
  EX R: hcy5_run, EX S: shim, EX m: val, EX c: val, EX rp: val, EX Q: hcy5_pkt,
  EX nonce: list byte, EX rr: list byte, EX CK: list byte, EX CM: cookie_msg,
  EX NS: list hnode4, EX PS: list (val * share * peer), EX T: tstate, EX np: val,
  EX CL: list (val * val * option cookie), EX KE: list kent4, EX CM': cookie_msg, EX honest: bool,
  EX now2: int64,
  PROPx [hcy5_reply_ok x25519 xaead_enc R L Q m nonce rr CK CM; hcy5_lists_ok L (map ke_addr KE) NS PS;
         hcy5_np_ok (hcy5_pubB x25519 R L) NS PS np; hcy5_T_ok PS KE T;
         hcy5_cl_nodes CL NS; hcy5_cl_snap CL PS; cm_ok CM';
         honest = true -> hcy5_honest_ok (hcy5_pubB x25519 R L) Q CM CM' NS PS T np;
         0 <= Int64.unsigned now2 < 2 ^ 62]
  (LOCALx ([temp HY._target (hcy5_p11_t0 NS CL T (cm_receiver CM'));
            temp HY._kes (hcy5_khead KE); temp HY._cns (hcy5_chead CL);
            temp HY._msg m; temp HY._copy c; temp HY._reply rp; temp HY._np np;
            temp HY._honest (Vint (if honest then Int.one else Int.zero));
            temp HY._head0 (hd nullval (t_L T)); temp HY._now (Vlong now2)] ++ hcy5_lvars gv L)
  (SEPx (hcy5_aside x25519 R L T (hnodes_snapped4 T NS PS) (peers_after PS (hcy5_res xaead_dec T PS CM' now2)) ++
         hcy5_bside x25519 R L (hcy5_CC2 x25519 R L Q rr) ++
         hcy5_bufs x25519 R L ++ hcy5_pbufs L Q m c rp ++
         [cmsg_rep Ews rp CM'; hbytes Tsh CK (l_cookie L); hbytes Tsh (cookie_msg_bytes CM') (l_img L);
          hcy5_cns (hcy5_chead CL) CL; kents_rep W (hcy5_khead KE) (map (kent_snapped T) KE);
          @data_at CKS Tsh t_devsnap (devsnap_val (hcy5_DA x25519 R L) (hcy5_phead PS)) (l_da L);
          @data_at_ W Tsh t_devsnap (l_db L); @data_at_ W Tsh t_skbsnap (l_sks L);
          @data_at CKS Tsh t_shimsnap (shimsnap_val S hcy5_w0) (l_ss L)] ++
         hcy5_scrB L ++ hcy5_globs gv S FR))).

End States.

(* the model's verdict once the target is known (used by segment C) *)
Definition hcy5_p11_newck (C: cookie) (now: int64) (pt: list byte) : cookie :=
  mkCookie now true pt false (ck_last_mac1 C) (ck_dkey C) (ck_mkey C).

(* NULL target: the model's target is NULL too *)
Lemma hcy5_p11_agree0 xaead_dec NS CL T PS CM' now2 :
  hcy5_p11_t0 NS CL T (cm_receiver CM') = nullval ->
  hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2) = nullval.
Proof.
  unfold hcy5_p11_t0, hcy5_tgt, hcy5_res, message_consume_model.
  destruct (t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver CM')) as [[a E]|]; [|reflexivity].
  intros H0. destruct (sfind PS (e_peer E)) as [[sh P]|]; [|reflexivity].
  destruct (negb (ck_sent (p_cookie P))); [reflexivity|].
  destruct (xaead_dec _ _ _ _); [exact H0 | reflexivity].
Qed.

(* ---------------------------------------------------------------------- *)
(* The agreement (v1 hcy4_p11_agree)                                       *)
(* ---------------------------------------------------------------------- *)

(* the cnode the search finds: its position in CL and its node's peer *)
Lemma hcy5_p11_agree_cfind NS CL p :
  hcy5_cfind NS CL p <> nullval ->
  exists CL1 nd o CL2, CL = CL1 ++ (hcy5_cfind NS CL p, nd, o) :: CL2 /\ hcy5_nodepeer NS nd = p.
Proof.
  induction CL as [|[[c nd] o] CL' IH]; simpl; intros H.
  - congruence.
  - destruct (EqDec_val (hcy5_nodepeer NS nd) p) as [e|ne].
    + exists [], nd, o, CL'. split; [reflexivity | exact e].
    + destruct (IH H) as (CL1 & nd' & o' & CL2 & E1 & E2).
      exists ((c, nd, o) :: CL1), nd', o', CL2. split; [simpl; f_equal; exact E1 | exact E2].
Qed.

Lemma hcy5_p11_agree_map_pair {A B C D: Type} (f: A -> C) (g: B -> D) (l1: list A) (l2: list B) :
  combine (map f l1) (map g l2) = map (fun '(a, b) => (f a, g b)) (combine l1 l2).
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros [|b l2]; simpl; try reflexivity.
  f_equal. apply IH.
Qed.

Lemma hcy5_p11_agree_combine_rev {A B: Type} (l1: list A) (l2: list B) :
  length l1 = length l2 -> combine (rev l1) (rev l2) = rev (combine l1 l2).
Proof.
  revert l2; induction l1 as [|a l1 IH]; intros [|b l2] Hl; simpl in *; try reflexivity; try discriminate.
  rewrite combine_app by (rewrite !rev_length; lia).
  rewrite IH by lia. reflexivity.
Qed.

Lemma hcy5_p11_agree_combine_self {A B C: Type} (l: list (A * B * C)) :
  combine (map (fun x => snd (fst x)) l) (map snd l) = map (fun x => (snd (fst x), snd x)) l.
Proof. induction l as [|x l IH]; simpl; [reflexivity | f_equal; exact IH]. Qed.

Lemma hcy5_p11_agree_in_combine_map {A B C: Type} (f: A -> C) (g: B -> C) (l1: list A) (l2: list B) a b :
  map f l1 = map g l2 -> In (a, b) (combine l1 l2) -> f a = g b.
Proof.
  revert l2; induction l1 as [|x l1 IH]; intros [|y l2] Hm Hin; simpl in *; try contradiction.
  inversion Hm; subst. destruct Hin as [Hin|Hin].
  - inversion Hin; subst; assumption.
  - eapply IH; eassumption.
Qed.

Lemma hcy5_p11_agree_nodepeer NS N :
  NoDup (map hn_addr NS) -> In N NS -> hcy5_nodepeer NS (hn_addr N) = hn_p N.
Proof.
  unfold hcy5_nodepeer. induction NS as [|N0 NS IH]; simpl; intros Hnd Hin; [contradiction|].
  inversion Hnd; subst.
  destruct (EqDec_val (hn_addr N0) (hn_addr N)) as [e|ne].
  - destruct Hin as [<-|Hin]; [reflexivity|].
    exfalso. apply H1. rewrite e. apply in_map. exact Hin.
  - destruct Hin as [<-|Hin]; [congruence|]. apply IH; assumption.
Qed.

Lemma hcy5_p11_agree_sfind (PS: list (val * share * peer)) a sh P :
  NoDup (map peer_addr4 PS) -> In (a, sh, P) PS -> sfind PS a = Some (sh, P).
Proof.
  induction PS as [|[[a0 sh0] P0] PS IH]; simpl; intros Hnd Hin; [contradiction|].
  inversion Hnd; subst.
  destruct (EqDec_val a0 a) as [e|ne].
  - destruct Hin as [Hin|Hin]; [inversion Hin; subst; reflexivity|].
    exfalso. apply H1. subst a0. change a with (peer_addr4 (a, sh, P)). apply in_map. exact Hin.
  - destruct Hin as [Hin|Hin]; [inversion Hin; congruence|]. apply IH; assumption.
Qed.

Lemma hcy5_p11_agree_snap_addr T N x :
  hn_addr (hn_snapshot4 T N x) = hn_addr N /\ hn_p (hn_snapshot4 T N x) = hn_p N.
Proof.
  destruct x as [[p sh] P]. unfold hn_snapshot4. split; reflexivity.
Qed.

Lemma hcy5_p11_agree xaead_dec L KS NS PS T CL CM' now2 :
  hcy5_lists_ok L KS NS PS -> hcy5_cl_nodes CL NS -> hcy5_cl_snap CL PS ->
  hcy5_p11_t0 NS CL T (cm_receiver CM') <> nullval ->
  exists a E P nd CL1 CL2 NS1 N NS2,
    t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver CM') = Some (a, E) /\
    sfind PS (e_peer E) = Some (Ews, P) /\
    CL = CL1 ++ (hcy5_p11_t0 NS CL T (cm_receiver CM'), nd, Some (p_cookie P)) :: CL2 /\
    hnodes_snapped4 T NS PS = NS1 ++ N :: NS2 /\ hn_addr N = nd /\ hn_p N = e_peer E /\
    hcy5_res xaead_dec T PS CM' now2 =
      (if ck_sent (p_cookie P) then
         match xaead_dec (ck_dkey (p_cookie P)) (cm_nonce CM') (ck_last_mac1 (p_cookie P)) (cm_enc CM') with
         | Some pt => Some (e_peer E, p_set_cookie P (hcy5_p11_newck (p_cookie P) now2 pt))
         | None => None
         end
       else None) /\
    hcy5_tgt NS CL (hcy5_res xaead_dec T PS CM' now2) =
      (if ck_sent (p_cookie P) then
         match xaead_dec (ck_dkey (p_cookie P)) (cm_nonce CM') (ck_last_mac1 (p_cookie P)) (cm_enc CM') with
         | Some _ => hcy5_p11_t0 NS CL T (cm_receiver CM')
         | None => nullval
         end
       else nullval).
Proof.
  intros [Hok [Hpeers [HndP [HndN _]]]] [Hcl1 Hcl2] Hsnap Ht0.
  assert (Hlen: length NS = length PS).
  { rewrite <- (map_length hn_p NS), <- (map_length peer_addr4 PS). f_equal. exact Hpeers. }
  unfold hcy5_p11_t0 in *.
  destruct (t_lookup T (Int.or IDX_HANDSHAKE IDX_KEYPAIR) (cm_receiver CM')) as [[a E]|] eqn:HL;
    [|congruence].
  destruct (hcy5_p11_agree_cfind NS CL (e_peer E) Ht0) as (CL1 & nd & o & CL2 & HCL & Hnp).
  (* the position of the cnode in CL: a node N and a peer x, at the same position of NS and PS *)
  assert (Hin: In (nd, o) (map (fun x => (snd (fst x), snd x)) CL)).
  { rewrite HCL, map_app. apply in_or_app. right. left. reflexivity. }
  rewrite <- hcy5_p11_agree_combine_self, Hcl1, Hsnap in Hin.
  rewrite hcy5_p11_agree_combine_rev in Hin by (rewrite !map_length; exact Hlen).
  rewrite <- in_rev, hcy5_p11_agree_map_pair, in_map_iff in Hin.
  destruct Hin as ([N [[p sh] P]] & HNx & HinNx). simpl in HNx. inversion HNx; subst nd o; clear HNx.
  pose proof (in_combine_l _ _ _ _ HinNx) as HinN.
  pose proof (in_combine_r _ _ _ _ HinNx) as HinP.
  pose proof (hcy5_p11_agree_in_combine_map _ _ _ _ _ _ Hpeers HinNx) as HpN. simpl in HpN.
  rewrite hcy5_p11_agree_nodepeer in Hnp by assumption.
  assert (Hsh: sh = Ews).
  { rewrite Forall_forall in Hok. destruct (Hok _ HinP) as [Hsh _]. exact Hsh. }
  subst sh.
  assert (HP: sfind PS (e_peer E) = Some (Ews, P)).
  { apply hcy5_p11_agree_sfind; [exact HndP|]. rewrite <- Hnp, HpN. exact HinP. }
  assert (HinS: In (hn_snapshot4 T N (p, Ews, P)) (hnodes_snapped4 T NS PS)).
  { unfold hnodes_snapped4. change (hn_snapshot4 T N (p, Ews, P))
      with ((fun '(N, x) => hn_snapshot4 T N x) (N, (p, Ews, P))). apply in_map. exact HinNx. }
  destruct (in_split _ _ HinS) as (NS1 & NS2 & HS).
  destruct (hcy5_p11_agree_snap_addr T N (p, Ews, P)) as [Ha Hp].
  exists a, E, P, (hn_addr N), CL1, CL2, NS1, (hn_snapshot4 T N (p, Ews, P)), NS2.
  split; [reflexivity|]. split; [exact HP|]. split; [exact HCL|]. split; [exact HS|].
  split; [exact Ha|]. split; [rewrite Hp; exact Hnp|].
  unfold hcy5_res, message_consume_model. rewrite HL, HP.
  destruct (ck_sent (p_cookie P)); simpl; [|split; reflexivity].
  destruct (xaead_dec _ _ _ _); [|split; reflexivity].
  split; [reflexivity|]. unfold hcy5_tgt. reflexivity.
Qed.
