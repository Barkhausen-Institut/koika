(*! Utilities | Finiteness typeclass !*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.

Class FiniteType {T} :=
  { finite_index: T -> nat;
    finite_elements: list T;
    finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
    finite_injective: NoDup (List.map finite_index finite_elements) }.
Arguments FiniteType: clear implicits.

Definition finite_index_injective {T: Type} {FT: FiniteType T}:
  forall t1 t2,
    finite_index t1 = finite_index t2 ->
    t1 = t2.
Proof.
  intros t1 t2 H.
  apply (f_equal (nth_error finite_elements)) in H.
  rewrite !finite_surjective in H.
  inversion H; auto.
Qed.

Definition finite_nodup {T} {FT: FiniteType T} :
  NoDup finite_elements.
Proof.
  eapply NoDup_map_inv.
  apply finite_injective.
Qed.

Fixpoint increasing (l: list nat) :=
  match l with
  | [] => true
  | n1 :: [] => true
  | n1 :: (n2 :: _) as l => andb (Nat.ltb n1 n2) (increasing l)
  end.

Lemma increasing_not_In :
  forall l n, increasing (n :: l) = true -> forall n', n' <= n -> ~ In n' l.
Proof.
  induction l; intros n H n' Hle Habs.
  - auto.
  - apply Bool.andb_true_iff in H; destruct H; apply PeanoNat.Nat.ltb_lt in H.
    destruct Habs as [ ? | ? ]; subst; try lia.
    eapply IHl; [ eassumption | .. | eassumption ]; lia.
Qed.

Lemma increasing_not_In' :
  forall l n, increasing (n :: l) = true -> forall n', n' <? n = true -> ~ In n' (n :: l).
Proof.
  unfold not; intros l n Hincr n' Hlt [ -> | Hin ]; apply PeanoNat.Nat.ltb_lt in Hlt.
  - lia.
  - eapply increasing_not_In;
      [ eassumption | apply Nat.lt_le_incl | eassumption ]; eauto.
Qed.

Lemma increasing_NoDup :
  forall l, increasing l = true -> NoDup l.
Proof.
  induction l as [ | n1 l IHl]; cbn; intros H.
  - constructor.
  - destruct l.
    + repeat constructor; inversion 1.
    + apply Bool.andb_true_iff in H; destruct H.
      constructor.
      apply increasing_not_In'; eauto.
      eauto.
Qed.

Lemma nth_error_nil_None {A} (n : nat) :
  List.nth_error (@nil A) n = None.
Proof.
  rewrite nth_error_None. auto with arith.
Qed.

Lemma add_schuffle (a b c: nat):
  a + b + c = b + c + a.
Proof.
  rewrite (@Nat.add_comm a b), Nat.add_shuffle0.
  reflexivity.
Qed.

Fixpoint nth_error_prod0 {A1} (l1: list A1):
  forall n x,
  nth_error l1 n = Some x ->
  nth_error l1 n = Some x.
Proof.
  intros. assumption.
Qed.

Fixpoint nth_error_prod {A1 A2} (l1: list A1) (l2 : list A2):
  forall n1 n2 x y,
  nth_error l1 n1 = Some x ->
  nth_error l2 n2 = Some y ->
  nth_error (list_prod l1 l2) (n1 * length l2 + n2) = Some (x,y).
Proof.
  intros n1 n2 x y H1 H2.
  destruct l1.
  - rewrite nth_error_nil_None in H1.
    discriminate.
  - destruct n1 as [| n1'].
    + rewrite Nat.mul_0_l in *.
      rewrite Nat.add_0_l in *.
      simpl (list_prod _).
      cbv beta.
      rewrite nth_error_app1.
      * rewrite nth_error_map.
        rewrite H2.
        simpl (option_map _ _).
        simpl in H1.
        inversion H1 as [H1'].
        reflexivity.
      * rewrite map_length.
        apply nth_error_Some.
        rewrite H2.
        discriminate.
    + simpl in H1.
      simpl (list_prod _).
      cbv beta.
      rewrite nth_error_app2.
      all: rewrite map_length.
      * simpl.
        rewrite add_schuffle.
        rewrite Nat.add_sub.
        apply (nth_error_prod); assumption.
      * simpl.
        auto with arith.
Qed.

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Fixpoint nth_error_app_l {A} (l l' : list A):
  forall n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  intros.
  erewrite nth_error_app1.
  - assumption.
  - apply nth_error_Some.
    rewrite H.
    discriminate.
Qed.

Fixpoint nth_error_app_r {A} (l l' : list A):
forall n x,
  nth_error l n = Some x ->
  nth_error (l' ++ l) (n + length l') = Some x.
Proof.
  intros.
  erewrite nth_error_app2.
  - rewrite Nat.add_sub. assumption.
  - auto with arith.
Qed.

Lemma nth_error_cons {A} (a : A) (l : list A):
forall x n,
  nth_error l n = Some x ->
  nth_error (a :: l) (S n) = Some x.
Proof.
intros.
simpl.
assumption.
Qed.

  (* nth_error (A'' :: map B'' finite_elements ++ ?l') ?Goal0 = Some C'' *)
Ltac FiniteType_t_clean_up_list :=
  lazymatch goal with
  | [ |- nth_error (_ :: _) _ = Some _ ] =>
    apply nth_error_cons; FiniteType_t_clean_up_list
  | [ |- nth_error (_ ++ _) _ = Some _ ] =>
    apply nth_error_app_r; FiniteType_t_clean_up_list
  | _ => idtac
  end.


(* (fun a      => A a)
(fun A '(a,b) => A a b)
(fun B '(a,b) => B a b)
(fun '((a,b),c) => A a b c) *)
(* ((fun A '((a,b),c) => A a b c) B'') *)
Ltac map_function_rec con :=
  lazymatch con with
  | ?f ?x ?y =>
    let y := (map_function_rec (f x)) in constr:((fun A '(a,b) => A a b) y)
  | ?f ?x => constr:(f)
  end.

(* (nth_error_prod _ _ _ _ _ _ (nth_error_prod _ _ _ _ _ _ (nth_error_prod0 _ _ _ _) _) _) *)
(* (nth_error_prod _ _ _ _ _ _ (nth_error_prod0 _ _ _ _) _). *)
Ltac prod_function_rec con :=
  lazymatch con with
  | ?f ?x ?y =>
    let y := (prod_function_rec (f x)) in uconstr:(nth_error_prod _ _ _ _ _ _ y _)
  | ?f ?x => uconstr:(nth_error_prod0 _ _ _ _)
  end.

Ltac FiniteType_t_compute_index :=
  FiniteType_t_clean_up_list;
  lazymatch goal with
  | [ |- nth_error _ _ = Some ?con ] =>
    match con with
    | _ _ =>
      apply nth_error_app_l;
      let func1 := map_function_rec con in
      rewrite (nth_error_map (func1));
      let func2 := prod_function_rec (con) in
      unshelve erewrite func2;
      lazymatch goal with 
      | [|-  _ = _ ] => idtac
      | _ => shelve
      end;
      [> .. | simpl; reflexivity];
      lazymatch goal with
      | [ |- _ = Some ?z ] =>
        let tz' := type of z in
        let tx := type of con in pose proof (finite_type_norec tx);
        eapply (finite_surjective (T := tz') (FiniteType := ltac:(typeclasses eauto)))
      end
    | _ =>
      instantiate (1 := 0);
      instantiate (1 := _ :: _)
      ;reflexivity
    end
  end.

Ltac FiniteType_t_nodup_increasing :=
  apply increasing_NoDup;
  vm_compute; reflexivity.

Ltac FiniteType_t_init :=
  unshelve econstructor;
    [ destruct 1; shelve | shelve | .. ].

Ltac FiniteType_t :=
  lazymatch goal with
  | [ H: FiniteType_norec ?T |- FiniteType ?T ] => fail "Type" T "is recursive"
  | [  |- FiniteType ?T ] =>
    let nm := fresh in
    unshelve econstructor;
    [ destruct 1; shelve
    | shelve
    | intros nm; destruct nm; [> FiniteType_t_compute_index ..]
    | instantiate (1 := []); FiniteType_t_nodup_increasing ]
  end.

Hint Extern 1 (FiniteType _) => FiniteType_t : typeclass_instances.

Module Examples.
  Inductive t0 := A0 | B0.
  Inductive t1 := A1 | B1 (x: t0) | C1.
  Inductive t2 := A2 | B2 (x: t1) | C2 | D2 (x: t0).
  Inductive t3 := A3 (x y: t2) (z: t1) | B3 (x y z: t0) | C3.

  Instance t0f : FiniteType t0 := _.
  Instance t1f : FiniteType t1 := _.
  Instance t2f : FiniteType t2 := _.
  Instance t3f : FiniteType t3 := _.

  Inductive t_recursive := A_r (x': t_recursive) (y': t0) | B_r.

  Fail Instance t_recursive_f : FiniteType t_recursive := _.

  Inductive t_mut_recursive : Set := 
  | A4 | B4 | C4 (x: t_mut2)
  with t_mut2 : Set :=
  | A5 | B5 (x1: t_mut_recursive) | C5.

  Fail Instance t_mut_recursive_f : FiniteType_t t_mut_recursive := _.
End Examples.
