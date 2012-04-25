
Section Ex1.

  (* Some helpful definitions and automatic coercions for later *)

  Definition rel := nat -> nat -> Prop.
  Identity Coercion rel_def: rel >-> Funclass.
  Definition func := nat -> nat.
  Identity Coercion func_def: func >-> Funclass.
  
  Definition npair : Type := (nat * nat)%type.
  Identity Coercion prod_of_npair : npair >-> prod.
  Hint Unfold npair.
  
  (* < . , . > *)
  Variable pair: npair -> nat.
  Variable pair_inj: forall x y, pair x = pair y -> x = y.

  Coercion pair: npair >-> nat.
  Hint Resolve pair.

  (* We choose ( . , . ) instead of < . , . > so
     we can write the more natural f (x,y) instead of
     f <x, y>. *)
  Notation "( a , b )" := ((a,b):npair).
  
  (* \pi_1 and \pi_2 *)
  Variable p1 p2: func.
  
  Notation "'\pi_1'" := (p1).
  Notation "'\pi_2'" := (p2).
             
  Variable p1_def: forall x y, \pi_1 (x, y) = x.
  Variable p2_def: forall x y, \pi_2 (x, y) = y.

  (* We define functionality *)
  Definition functional (f: rel) :=
    forall x y z, f x y -> f x z -> y = z.
  
  (* We define the type of partial functions
     to be all binary relations on natural numbers
     that satisfy functionality. *)
  Record pfunction : Type :=
    pfuncI {
        pfunc :> rel;
        pfunctional : functional pfunc
      }.

  (* We define reducability on any binary
     relation on natural numbers. *)
  Definition reducible (f: rel) :=
    forall x, { y | f x y }.
  
  (* We define the type of total functions
     to be all partial functions that satisfy
     reducability. *)
   Record tfunction : Type :=
    tfuncI {
        tfunc :> pfunction;
        treducible: reducible tfunc
      }.

  (* We define semi-decidability *)

  Definition semidecides (f: nat -> nat) (p: pfunction) :=
    forall x y, p x y <-> f x = y.

  Notation "f 'semi-decides' p" := (semidecides f p) (at level 8).

  (* We define the type of partial computable
     functions to be all semi-decidable partial
     functions. *)
  Record pcfunction : Type :=
    pcfuncI {
        pcfunc :> pfunction;
        pcsemdec: nat -> nat;
        pcomp: pcsemdec semi-decides pcfunc
      }.
  
  (* We define total computable functions to be
     reducible partial computable functions. *)
  Record tcfunction : Type :=
    tcfuncI {
        tcfunc :> pcfunction;
        tcreducible : reducible tcfunc
      }.

  (* We define a coercion from total computable
     functions to normal Coq functions. *)
  Definition tcf (f: tcfunction) : nat -> nat.
    intros x. destruct (tcreducible f x). exact x0. Defined.

  
  (* We define the type of turing machines to
     be the natural numbers, i.e. we only deal
     with encoded turing machines.

     We also define some coercions between
     TMs and partial/computable/total functions *)
  
  Definition TM : Type := nat.
  Identity Coercion nat_of_TM : TM >-> nat.

  Variable TM_of_tf: tfunction -> TM.
  Coercion TM_of_tf: tfunction >-> TM.
  Definition nat_of_tf f := nat_of_TM (TM_of_tf f).
  Coercion nat_of_tf: tfunction >-> nat.

  Variable TM_of_pcf: pcfunction -> TM.
  Coercion TM_of_pcf: pcfunction >-> TM.
  Definition nat_of_pcf f := nat_of_TM (TM_of_pcf f).
  Coercion nat_of_pcf: pcfunction >-> nat.

  
  (* Encoding *)
  Variable enc: pcfunction -> TM.
  Coercion enc: pcfunction >-> TM.

  (* Decoding *)
  Variable phi: TM -> pcfunction.
  Coercion phi: TM >-> pcfunction.

  Notation "'\phi_' p" := (phi p)
  (at level 8, p at level 2, format "'\phi_' p").
  
  (* Correctness of phi and enc. *)
  Variable phi_enc: forall f, phi (enc f) = f.
  
  (* We assume the existence of a step function
     that simulates a TM on some input
     for some number of steps. *)
  Variable step: TM -> nat -> nat -> option nat.
  Variable step_def: forall (t: TM) x y, t x y <-> exists n, step t x n = Some y. 
  Variable step_monotone: forall t x n n' y, step t x n = Some y -> n' > n -> step t x n' = Some y.

  (* We define big Phi. *)
  Variable Phi: forall (p: TM), pcfunction.
  Variable Phi_def: forall p x n t, (forall m, m < n -> step p x n = None) -> step p x n = Some t -> Phi p x n.

  Notation "'\Phi_' p" := (Phi p)
  (at level 8, p at level 2, format "'\Phi_' p").


  Record effop :=
    effopI {
        Theta :> pcfunction -> pcfunction;
        effop_f: tfunction;
        effop_def: forall e, Theta (\phi_e) = \phi_(effop_f e)
    }.


  Variable pad: tfunction.
  Variable pad_inj: forall (x y: npair), pad x = pad y -> x = y.
  Print Coercions.
  Variable pad_def: forall (p: nat) (x: nat), \phi_(pad (p,x)) = \phi_p.

  Variable snm: tfunction.
  Variable snm_def: forall e x y, \phi_(snm (e,x)) y = \phi_e (x,y).
  Variable snm_inj: forall x y, snm x = snm y -> x = y.

  Variable krt: tfunction.
  Variable krt_def: forall p x, \phi_(krt p) x = \phi_p (krt p, x).
  Variable krt_def': forall (f: pcfunction) x, \phi_krt x = f (krt:nat, x).
  
  Variable rft_def: forall f, exists e, \phi_(f e) = \phi_e.

  Variable ort_def: forall (Theta: effop), exists e:tfunction, forall n x, \phi_(e n) x = Theta e (n,x).

  Variable univ: TM.
  Variable univ_def: forall p x, \phi_univ (p,x) = \phi_p(x).

  
  Variable div: pfunction -> Prop.

  Definition computes (f: pfunction) (g: tfunction) := forall x y, f x y <-> g x = y.

  Notation "f 'computes' g" := (f computes g) (at level 70).

  (*
  Definition halts f x : pfunction := 
  
  Variable halting_not_computable:
  *)


  (* 2.2 Examples *)

  
  
  Variable Thm211: exists r: tfunction, forall sigma e x: list nat,
                                          \phi_(r (sigma,e)) x = match leqb
  
End Ex1.