(* law prim_aead: check_decrypt_any of prim_aead.h: the cut of the body into segments A..D and the
   states between them. *)
Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import VST.floyd.VSU.
Require Import QuickProof.Contract.
Require WgNoise.units.Noise WgNoise.units.Cookie WgNoise.units.Counter WgNoise.units.Blake2s WgNoise.units.Chacha WgNoise.units.ChachaBlock WgNoise.units.Poly1305 WgNoise.units.Poly1305Donna32 WgNoise.units.Chacha20poly1305 WgNoise.units.Curve25519 WgNoise.units.Curve25519Fiat32 WgNoise.units.Shim WgNoise.units.Libc WgNoise.units.Malloc.
Require Import WgNoise.proof.common.wg3_worlds.
Require Import WgNoise.proof.prims.prim_api.
Require Import WgNoise.proof.blake2s.spec_shared.
Require Import WgNoise.proof.harness.prim_aead.haead_spec3.
Require Import WgNoise.proof.harness.prim_aead.haead_lemmas3.
Require WgNoise.harness.x_prim_aead.code.

#[local] Existing Instance W_prim_aead.
Local Open Scope Z_scope.

(* ---------------------------------------------------------------------- *)
(* the body, cut into segments                                             *)
(* ---------------------------------------------------------------------- *)

Module CD := WgNoise.harness.x_prim_aead.code.

Definition cda_body : statement :=
  Eval cbv beta iota delta [CD.f_check_decrypt_any fn_body] in fn_body CD.f_check_decrypt_any.

Fixpoint cda_drop (n: nat) (s: statement) : statement :=
  match n with O => s | S n' => match s with Ssequence _ r => cda_drop n' r | _ => Sskip end end.
Fixpoint cda_heads (n: nat) (s: statement) : list statement :=
  match n with O => nil | S n' => match s with Ssequence a r => a :: cda_heads n' r | _ => nil end end.
Fixpoint cda_seqs (l: list statement) (r: statement) : statement :=
  match l with nil => r | s :: l' => Ssequence s (cda_seqs l' r) end.

(* A: the first if (c2 drawn); B: dn, the three mallocs, the NULL test; C: nondet_bytes, the copy, the
   two decryptions; D: the checks and the frees *)
Definition cda_A : statement :=
  Eval cbv beta iota zeta delta [cda_heads cda_body] in hd Sskip (cda_heads 1 cda_body).
Definition cda_lB : list statement :=
  Eval cbv beta iota zeta delta [cda_heads cda_drop cda_body] in cda_heads 5 (cda_drop 1 cda_body).
Definition cda_lC : list statement :=
  Eval cbv beta iota zeta delta [cda_heads cda_drop cda_body] in cda_heads 4 (cda_drop 6 cda_body).
Definition cda_D : statement :=
  Eval cbv beta iota zeta delta [cda_drop cda_body] in cda_drop 10 cda_body.

Lemma cda_body_eq : cda_body = Ssequence cda_A (cda_seqs cda_lB (cda_seqs cda_lC cda_D)).
Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------- *)
(* the states between the segments                                         *)
(* ---------------------------------------------------------------------- *)

Definition cda_Delta : tycontext := func_tycontext CD.f_check_decrypt_any haead_V haead_Gprog nil.

(* the model's verdict on the drawn ciphertext c *)
Definition cda_dec (x: Z) (key: list byte) (nonce: Z) (xnonce a c: list byte) : option (list byte) :=
  if Int.eq (Int.repr x) Int.zero then aead_dec key nonce a c else xaead_dec key xnonce a c.
Definition cda_b (d: option (list byte)) : int := match d with Some _ => Int.one | None => Int.zero end.
Definition cda_out (d: option (list byte)) (bs: list byte) : list val :=
  match d with Some pt => map Vubyte pt | None => map Vubyte bs end.
(* rd2 after the reference decryption: the plaintext, or still uninitialised on rejection *)
Definition cda_rout (d: option (list byte)) (n: Z) : list val :=
  match d with Some pt => map Vubyte pt | None => Zrepeat Vundef n end.

Definition cda_R (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals)
  : ret_assert :=
  frame_ret_assert
    (function_body_ret_assert tvoid
       (PROP () RETURN ()
        SEP (data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
             data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
             data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
             data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
             mem_mgr gv; zero_page gv; haead_globals gv)))
    (stackframe_of CD.f_check_decrypt_any).

Definition cda_P0 (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals)
  : environ -> mpred :=
  PROP ()
  LOCAL (gvars gv; temp CD._x (Vint (Int.repr x)); temp CD._key kp; temp CD._nonce (Vlong (Int64.repr nonce));
         temp CD._xnonce xp; temp CD._ad ad; temp CD._adlen (Vlong (Int64.repr (Zlength a)));
         temp CD._ct cp; temp CD._n (Vlong (Int64.repr (Zlength ct - 16))))
  SEP (data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
       data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
       data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
       data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
       mem_mgr gv; zero_page gv; haead_globals gv).

(* after A: c2 holds the drawn ciphertext c (m = |c|) *)
Definition cda_P1 (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals)
  (c: list byte) (c2: val) : environ -> mpred :=
  PROP (Zlength c <= Int64.max_signed)
  LOCAL (temp CD._m (Vlong (Int64.repr (Zlength c))); temp CD._c2 c2;
         gvars gv; temp CD._x (Vint (Int.repr x)); temp CD._key kp; temp CD._nonce (Vlong (Int64.repr nonce));
         temp CD._xnonce xp; temp CD._ad ad; temp CD._adlen (Vlong (Int64.repr (Zlength a))))
  SEP (malloc_token Ews (tarray tuchar (Zlength c)) c2;
       data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) c2;
       data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
       data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
       data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
       data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
       mem_mgr gv; zero_page gv; haead_globals gv).

(* after B: the three buffers of dn = max 0 (|c| - 16) bytes, none NULL *)
Definition cda_P2 (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals)
  (c: list byte) (c2 d2 db rd2: val) : environ -> mpred :=
  PROP (Zlength c <= Int64.max_signed)
  LOCAL (temp CD._dn (Vlong (Int64.repr (Z.max 0 (Zlength c - 16))));
         temp CD._d2 d2; temp CD._d2_before db; temp CD._rd2 rd2;
         temp CD._m (Vlong (Int64.repr (Zlength c))); temp CD._c2 c2;
         gvars gv; temp CD._x (Vint (Int.repr x)); temp CD._key kp; temp CD._nonce (Vlong (Int64.repr nonce));
         temp CD._xnonce xp; temp CD._ad ad; temp CD._adlen (Vlong (Int64.repr (Zlength a))))
  SEP (malloc_token Ews (tarray tuchar (Zlength c)) c2;
       data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) c2;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) d2;
       data_at_ Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) d2;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) db;
       data_at_ Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) db;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) rd2;
       data_at_ Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) rd2;
       data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
       data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
       data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
       data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
       mem_mgr gv; zero_page gv; haead_globals gv).

(* after C: d2 drawn as bs and copied to d2_before; both decryptions done (ok = rok = the model's verdict);
   rd2 is written only on acceptance *)
Definition cda_P3 (x: Z) (ksh: share) (kp: val) (key: list byte) (nonce: Z) (xsh: share) (xp: val) (xnonce: list byte)
  (ash: share) (ad: val) (a: list byte) (csh: share) (cp: val) (ct: list byte) (gv: globals)
  (c: list byte) (c2 d2 db rd2: val) (bs: list byte) : environ -> mpred :=
  PROP (Zlength c <= Int64.max_signed; Zlength bs = Z.max 0 (Zlength c - 16))
  LOCAL (temp CD._ok (Vint (cda_b (cda_dec x key nonce xnonce a c)));
         temp CD._rok (Vint (cda_b (cda_dec x key nonce xnonce a c)));
         temp CD._dn (Vlong (Int64.repr (Z.max 0 (Zlength c - 16))));
         temp CD._d2 d2; temp CD._d2_before db; temp CD._rd2 rd2; temp CD._c2 c2; gvars gv)
  SEP (malloc_token Ews (tarray tuchar (Zlength c)) c2;
       data_at Ews (tarray tuchar (Zlength c)) (map Vubyte c) c2;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) d2;
       data_at Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) (cda_out (cda_dec x key nonce xnonce a c) bs) d2;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) db;
       data_at Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) (map Vubyte bs) db;
       malloc_token Ews (tarray tuchar (Z.max 0 (Zlength c - 16))) rd2;
       data_at Ews (tarray tuchar (Z.max 0 (Zlength c - 16)))
         (cda_rout (cda_dec x key nonce xnonce a c) (Z.max 0 (Zlength c - 16))) rd2;
       data_at ksh (tarray tuchar 32) (map Vubyte key) kp;
       data_at xsh (tarray tuchar 24) (map Vubyte xnonce) xp;
       data_at ash (tarray tuchar (Zlength a)) (map Vubyte a) ad;
       data_at csh (tarray tuchar (Zlength ct)) (map Vubyte ct) cp;
       mem_mgr gv; zero_page gv; haead_globals gv).

