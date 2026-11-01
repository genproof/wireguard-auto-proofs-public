(* law handshake_receive: phase B8, branch R, segment B: the cut of statement 7 of branch R (hrx5_B8R_B) into sub-segments, their states and the pure
   statement that gives their facts.

   hrx5_B8R_B = if (!alloc_ok) FAIL else ELSE, with
     FAIL = C1 ; C2 ; C3            (C1 = CHECK allocs/frees/failures, C2 = CHECK state/remote_ephemeral/hash/ck/
                                    remote_index, C3 = CHECK h's entry and the other fields vs the snapshot s)
     ELSE = Z ; if (session) SESS else DEAD
       Z    = CHECK(hs_zeroed_from(s, h) && allocs + 1 && failures same)
       SESS = KP ; K1 ; K2 ; CLR    (KP = `t'280 = target->p; kp = t'280->keypairs.current_keypair`,
                                    K1 = CHECK(!h->entry.hashed && frees same), K2 = the keypair CHECK,
                                    CLR = wg_noise_keypairs_clear(&target->p->keypairs); CHECK(frees + 1))
       DEAD = CHECK(h->entry.hashed && h->entry.index == s->index && frees + 1)

   States (hrx5_B8R_St with the temps hrx5_B8R_tl tg a d P 0; W1 = the world after dispatch, Wx = the final one):
     Sf  = St W1 tl (G ++ FF)                     the failed allocation (FAIL: Sf -> Sf, each of C1 C2 C3)
     Sa  = St W1 tl (G ++ FA)                     the allocation succeeded (Z: Sa -> Sa)
     Sn  = St W1 tl (G ++ FA ++ [sess = false])   P dead (DEAD: Sn -> Sn)
     Ss  = St W1 tl (G ++ FA ++ (sess = true :: FS))       a session (KP: Ss -> Ssk)
     Ssk = St W1 (tl ++ [temp _kp k]) (G ++ FA ++ (sess = true :: FS))  (K1, K2: Ssk -> Ssk)
     Sx  = St Wx tl []                            after the harness's wg_noise_keypairs_clear (CLR: Ssk -> Sx)
   G = the facts of the branch (hrx5_B8R_facts without the world equation) + the target node's snapshot, the
   handshake entry in T, the counters of S1 (the shim after validate) = S's;
   FF / FA / FS = the world after dispatch in the three cases, explicitly (hrx5_B8RB_FF / FA / FS).
   Pure statement (child): hrx5_B8RB_pure_stmt (St's PROPs + hrx5_B8R_facts + itable_wf of W1's table give G and
   FF / FA; FS needs NoDup (t_L T) in addition: see of the note, a fact the parent's states lack). *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import VST.msl.iter_sepcon.
Require Import QuickProof.Contract.
Require Import QuickProof.Env.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.pieces.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.protocol.prot_model3.
Require Import WgNoise.proof.protocol.prot_repr3.
Require Import WgNoise.proof.protocol4.prot_repr4.
Require Import WgNoise.proof.protocol4.prot_model4.
Require Import WgNoise.proof.protocol4.prot_specs4.
Require Import WgNoise.proof.harness.common.hc_model3.
Require Import WgNoise.proof.harness.common.hc_specs3.
Require Import WgNoise.proof.harness.common4.hc4_model.
Require Import WgNoise.proof.harness.common4.hc4_specs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_world.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_cut.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_model.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_spec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mspec.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mci.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_mcr.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_hmodel.
Require WgNoise.contracts.x_handshake_receive.
Require WgNoise.harness.x_handshake_receive.code.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_conv.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_defs.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_ilem.
Require Import WgNoise.proof.harness.handshake_receive.hrx5_B8_R_defs.
#[local] Existing Instance W_handshake_receive.
Local Open Scope logic.

(* ---------------------------------------------------------------------- *)
(* the statements                                                          *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RB_C1 := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ (Ssequence ?x _) _ => exact x end).
Definition hrx5_B8RB_C2 := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ (Ssequence _ (Ssequence ?x _)) _ => exact x end).
Definition hrx5_B8RB_C3 := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ (Ssequence _ (Ssequence _ ?x)) _ => exact x end).
Definition hrx5_B8RB_Z := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence ?x _) => exact x end).
Definition hrx5_B8RB_KP := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ (Ssequence ?x _) _)) => exact x end).
Definition hrx5_B8RB_K1 := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence ?x _)) _)) => exact x end).
Definition hrx5_B8RB_K2 := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ (Ssequence ?x _))) _)) => exact x end).
Definition hrx5_B8RB_CLR := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ (Ssequence _ (Ssequence _ (Ssequence _ ?x))) _)) => exact x end).
Definition hrx5_B8RB_DEAD := ltac:(match eval cbv delta [hrx5_B8R_B] in hrx5_B8R_B with
  | Sifthenelse _ _ (Ssequence _ (Sifthenelse _ _ ?x)) => exact x end).

Lemma hrx5_B8RB_eq :
  hrx5_B8R_B =
  Sifthenelse (Eunop Onotbool (Etempvar HM._alloc_ok tint) tint)
    (Ssequence hrx5_B8RB_C1 (Ssequence hrx5_B8RB_C2 hrx5_B8RB_C3))
    (Ssequence hrx5_B8RB_Z
       (Sifthenelse (Etempvar HM._session tint)
          (Ssequence hrx5_B8RB_KP (Ssequence hrx5_B8RB_K1 (Ssequence hrx5_B8RB_K2 hrx5_B8RB_CLR)))
          hrx5_B8RB_DEAD)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the model of the three cases                                            *)
(* ---------------------------------------------------------------------- *)

(* the shim after validate (its rotation's draw) *)
Definition hrx5_B8RB_S1 (x25519: list byte -> list byte -> list byte) (R: hrx5_run) (L: hrx5_loc) (sec: list byte)
  (birth: int64) (S: shim) (q: int) (lul: int64) (o: hrx5_obj) (d: rxdraw) : shim :=
  hrx5_B8R_S1 (hrx5_DL x25519 R L sec birth) S q lul (obj_bytes o) d.

(* the accepted peer after begin_session when the allocation succeeded (refs back): zeroed, and in a session
   the new keypair rd_k d current *)
Definition hrx5_B8RB_Pz (d: rxdraw) (P: peer) (M: resp_msg) (ck h: list byte) : peer :=
  let Pn := hrx5cr_new P M ck h in
  let Z := p_set_refs (p_set_hs Pn (hs_zero (p_hs Pn))) (p_refs P) in
  if hrx5_B8R_sess d P then p_set_slots Z (rd_k d) nullval nullval else Z.

(* the table after a session: the keypair's entry k added, then replacing the handshake's entry *)
Definition hrx5_B8RB_T3 (T: tstate) (a k: val) : tstate :=
  snd (t_replace (t_add T k Ews (mkEntry a IDX_KEYPAIR Int.zero)) (hs_addr a) k).

(* the new keypair (begin_session's kp_new: initiator, boot time of S1) *)
Definition hrx5_B8RB_K (P: peer) (M: resp_msg) (ck h: list byte) (kc: int64) (S1: shim) : keypair :=
  kp_new (p_hs (hrx5cr_new P M ck h)) (Int64.add kc Int64.one) (s_boot S1).

(* G: the branch's facts, the target node's snapshot, P's handshake entry in T, S1's counters *)
Definition hrx5_B8RB_G (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte)) (R: hrx5_run) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (S S1: shim) (o: hrx5_obj) (tg: val) (ai ar: Z)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : list Prop :=
  [o = OResp M; hrx5_fwd (obj_bytes o) = true; ai = 0; ar = 1;
   hrx5cr_tgt x25519 aead_dec (hrx5_ID x25519 R) T PS M = Some (a, P, ck, h);
   0 <= j < Zlength PS; Znth j PS = (a, Ews, P); hn_p (Znth j NS) = a; tg = hn_addr (Znth j NS);
   Zlength NS = Zlength PS;
   Znth j (hnodes_snapped4 T NS PS) = mkHN4 tg a (hsnap_val (hs_snap_cur T a P)) (Vint (p_refs P)) (prsnap_val P);
   sfind (t_D T) (hs_addr a) = Some (Ews, t_entry_d T (hs_addr a));
   vin (hs_addr a) (t_L T) = true;
   e_peer (t_entry_d T (hs_addr a)) = a; e_type (t_entry_d T (hs_addr a)) = IDX_HANDSHAKE;
   s_allocs S1 = s_allocs S; s_fails S1 = s_fails S; s_frees S1 = s_frees S].

(* FF: the allocation failed: consume_response's state, refs back, nothing else; the final world is W1 *)
Definition hrx5_B8RB_FF (W1 Wx: rxw) (S1: shim) (T: tstate) (PS: list (val * share * peer)) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) : list Prop :=
  [hrx5_B8R_alloc d = false; rw_T W1 = T; rw_PS W1 = supd PS a (p_set_refs (hrx5cr_new P M ck h) (p_refs P));
   rw_KS W1 = []; rw_S W1 = shim_alloc_fail S1; Wx = W1].

(* FA: the allocation succeeded *)
Definition hrx5_B8RB_FA (W1 Wx: rxw) (S1: shim) (T: tstate) (PS: list (val * share * peer)) (kc: int64)
  (d: rxdraw) (a: val) (P: peer) (M: resp_msg) (ck h: list byte) : list Prop :=
  let sess := hrx5_B8R_sess d P in
  let Pz := hrx5_B8RB_Pz d P M ck h in
  [hrx5_B8R_alloc d = true; rw_PS W1 = supd PS a Pz;
   rw_T W1 = (if sess then hrx5_B8RB_T3 T a (rd_k d) else T);
   rw_KS W1 = (if sess then [(rd_k d, hrx5_B8RB_K P M ck h kc S1)] else []);
   rw_S W1 = (if sess then shim_alloc_ok S1 else shim_free (shim_alloc_ok S1));
   In (hs_addr a) (saddrs (t_D (rw_T W1)));
   sfind (t_D (rw_T W1)) (hs_addr a) = Some (Ews, t_entry_d T (hs_addr a));
   zeroed_from (hs_snap_cur T a P) (hs_snap_cur (rw_T W1) a Pz) = true;
   sess = false -> Wx = W1].

(* FS: a session (in addition to FA) *)
Definition hrx5_B8RB_FS (W1 Wx: rxw) (S1: shim) (T: tstate) (PS: list (val * share * peer)) (kc: int64)
  (d: rxdraw) (a: val) (P: peer) (M: resp_msg) (ck h: list byte) : list Prop :=
  let k := rd_k d in
  let T3 := hrx5_B8RB_T3 T a k in
  let K := hrx5_B8RB_K P M ck h kc S1 in
  let Pz := hrx5_B8RB_Pz d P M ck h in
  let KW := mkKW [(k, K)] T3 (shim_alloc_ok S1) in
  [k <> nullval; vin (hs_addr a) (t_L T3) = false; vin k (t_L T3) = true;
   sfind (t_D T3) k = Some (Ews, mkEntry a IDX_KEYPAIR (e_index (t_entry_d T (hs_addr a))));
   kp_init K = true; kp_rindex K = rm_sender M; kp_refs K = Int.one;
   keypairs_clear_model Pz KW =
     (hrx5_B8R_Pf d P M ck h, mkKW [] (t_remove T (hs_addr a)) (shim_free (shim_alloc_ok S1)));
   keypairs_clear_warn Pz KW (rw_w W1) = rw_w W1;
   Wx = mkRW (rw_D W1) (t_remove T (hs_addr a)) (supd PS a (hrx5_B8R_Pf d P M ck h)) []
          (shim_free (shim_alloc_ok S1)) (rw_w W1) (rw_kc W1) (rw_lul W1) (rw_rx W1)].

(* ---------------------------------------------------------------------- *)
(* the states (full binder lists, as hrx5_B8R_seg takes them)              *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RB_Sf (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St W1 tl (G ++ hrx5_B8RB_FF W1 Wx S1 T PS d a P M ck h).

Definition hrx5_B8RB_Sa (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St W1 tl (G ++ hrx5_B8RB_FA W1 Wx S1 T PS kc d a P M ck h).

Definition hrx5_B8RB_Sn (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St W1 tl (G ++ hrx5_B8RB_FA W1 Wx S1 T PS kc d a P M ck h ++ [hrx5_B8R_sess d P = false]).

Definition hrx5_B8RB_Ss (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St W1 tl (G ++ hrx5_B8RB_FA W1 Wx S1 T PS kc d a P M ck h ++ ((hrx5_B8R_sess d P = true) :: hrx5_B8RB_FS W1 Wx S1 T PS kc d a P M ck h)).

Definition hrx5_B8RB_Ssk (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St W1 (tl ++ [temp HM._kp (rd_k d)])
     (G ++ hrx5_B8RB_FA W1 Wx S1 T PS kc d a P M ck h ++ ((hrx5_B8R_sess d P = true) :: hrx5_B8RB_FS W1 Wx S1 T PS kc d a P M ck h)).

Definition hrx5_B8RB_Sx (x25519: list byte -> list byte -> list byte)
  (aead_dec: list byte -> Z -> list byte -> list byte -> option (list byte))
  (xaead_enc: list byte -> list byte -> list byte -> list byte -> list byte)
  (xaead_dec: list byte -> list byte -> list byte -> list byte -> option (list byte))
  (gv: globals) (L: hrx5_loc) (FR: mpred)
  (R: hrx5_run) (sec: list byte) (birth: int64) (S: shim) (w: list int64) (NS: list hnode4)
  (PS: list (val * share * peer)) (T: tstate) (head nk: val) (KE: list kent4) (st i: Z) (kc lul: int64) (q: int)
  (proto: Z) (ip4 ip6 port: list byte) (o: hrx5_obj) (dp img tg: val) (ai ar: Z) (d: rxdraw)
  (a: val) (P: peer) (M: resp_msg) (ck h: list byte) (j: Z) : environ -> mpred :=
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  let G := hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j in
  let St := hrx5_B8R_St x25519 aead_dec xaead_enc xaead_dec gv L FR R sec birth S w NS PS T head nk KE st i kc lul q
              proto ip4 ip6 port o dp img tg ai ar d in
  let tl := hrx5_B8R_tl tg a d P 0 in
  St Wx tl [].

(* ---------------------------------------------------------------------- *)
(* the pure statement                                                      *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RB_pure_stmt : Prop :=
  forall x25519 aead_enc aead_dec xaead_enc xaead_dec (L: hrx5_loc)
    R sec birth S w NS PS T head nk KE st i kc lul q proto ip4 ip6 port o dp tg ai ar d a P M ck h j,
  hrx5_hyps x25519 aead_enc aead_dec xaead_enc xaead_dec ->
  hrx5_base_ok R sec birth S -> hrx5_inv x25519 R L NS PS KE T head nk -> 0 <= st <= Int64.max_unsigned ->
  0 <= i < st -> obj_ok o -> malloc_compatible (Zlength (obj_bytes o)) dp ->
  hrx5_acc_ok x25519 aead_dec xaead_dec R NS PS T o (s_boot S) tg ai ar -> rxdraw_ok T d ->
  fold_right and True
    (hrx5_B8R_facts x25519 aead_dec xaead_enc xaead_dec L R sec birth S w NS PS T kc lul q proto ip4 ip6 port o dp
       tg ai ar d a P M ck h j) ->
  let W1 := hrx5_B8R_W1 x25519 aead_dec xaead_enc xaead_dec L R sec birth S w PS T kc lul q proto ip4 ip6 port o dp d in
  let Wx := hrx5_B8R_Wx W1 d T PS a P M ck h in
  let S1 := hrx5_B8RB_S1 x25519 R L sec birth S q lul o d in
  itable_wf (rw_T W1) ->
  fold_right and True (hrx5_B8RB_G x25519 aead_dec R NS PS T S S1 o tg ai ar a P M ck h j) /\
  (hrx5_B8R_alloc d = false -> fold_right and True (hrx5_B8RB_FF W1 Wx S1 T PS d a P M ck h)) /\
  (hrx5_B8R_alloc d = true -> fold_right and True (hrx5_B8RB_FA W1 Wx S1 T PS kc d a P M ck h)) /\
  (hrx5_B8R_sess d P = true -> NoDup (t_L T) -> fold_right and True (hrx5_B8RB_FS W1 Wx S1 T PS kc d a P M ck h)).

(* ---------------------------------------------------------------------- *)
(* the segment statements *)
(* ---------------------------------------------------------------------- *)

Definition hrx5_B8RB_C1_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Sf hrx5_B8RB_Sf hrx5_B8RB_C1 false.
Definition hrx5_B8RB_C2_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Sf hrx5_B8RB_Sf hrx5_B8RB_C2 false.
Definition hrx5_B8RB_C3_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Sf hrx5_B8RB_Sf hrx5_B8RB_C3 false.
Definition hrx5_B8RB_Z_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Sa hrx5_B8RB_Sa hrx5_B8RB_Z false.
Definition hrx5_B8RB_DEAD_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Sn hrx5_B8RB_Sn hrx5_B8RB_DEAD false.
Definition hrx5_B8RB_KP_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Ss hrx5_B8RB_Ssk hrx5_B8RB_KP false.
Definition hrx5_B8RB_K1_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Ssk hrx5_B8RB_Ssk hrx5_B8RB_K1 false.
Definition hrx5_B8RB_K2_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Ssk hrx5_B8RB_Ssk hrx5_B8RB_K2 false.
Definition hrx5_B8RB_CLR_stmt : Prop := hrx5_B8R_seg hrx5_B8RB_Ssk hrx5_B8RB_Sx hrx5_B8RB_CLR false.
