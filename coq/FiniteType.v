(*! Utilities | Finiteness typeclass !*)
Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.Arith.Arith.
Import ListNotations.

Class FiniteType {T} := {
  finite_index: T -> nat;
  finite_elements: list T;
  (* Caution: used for computations *)
  finite_surjective: forall a: T, List.nth_error finite_elements (finite_index a) = Some a;
  finite_injective: NoDup (List.map finite_index finite_elements)
}.
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


(* Caution: finite_surjective in used for computations
 *
 * Consequently, its proof term may only contain
 * transparent lemmas. For that, some lemmas from the
 * standard lib are redefined here, but transparent.
 *)

(* This definition provides a trick to create transparent
 * lemmas from opaque ones. (Only works with equalities on nat)
 *
 * This trick is taken from MIT-PLV's blog
 * https://github.com/mit-plv/blog/blob/b484ee3a87445e4d97b8a25b7614856a66354290/content/2020-06-17_computing-with-opaque-proofs.rst
 *)
Definition computational_eq {m n} (opaque_eq: m = n) : m = n :=
  match Nat.eq_dec m n with
  | left transparent_eq => transparent_eq
  | _ => opaque_eq (* dead code; could use [False_rect] *)
  end.

Lemma add_schuffle (a b c: nat):
  a + b + c = b + c + a.
Proof.
  induction a as [|a' IH]in b, c |- *;
  [..|cbn; rewrite IH];
  auto with arith.
Qed.

(* Transparent proofs of opaque ones *)
Definition add_schuffle_trans (a b c: nat) := computational_eq (add_schuffle a b c).
Definition add_sub_trans (m n : nat) := computational_eq (Nat.add_sub m n).

Lemma nth_error_prod0 {A1} (l1: list A1) (n : nat) (x : A1):
  nth_error l1 n = Some x ->
  nth_error l1 n = Some x.
Proof. trivial. Defined.

(* Taken from coq's standard lib + made transparent *)
Theorem le_n_S_trans : forall n m, n <= m -> S n <= S m.
Proof. induction 1; constructor; trivial. Defined.
Theorem le_pred_trans : forall n m, n <= m -> pred n <= pred m.
Proof. induction 1 as [|m _]; auto. destruct m; simpl; auto.
Defined.
Definition le_S_n_trans (n m : nat) : S n <= S m -> n <= m :=
  (le_pred_trans (S n) (S m)).


Fixpoint nth_error_app1_trans {A} (l l' : list A) n:
  n < length l ->
  nth_error (l ++ l') n = nth_error l n.
Proof.
  intros.
  destruct l, n; cbn in H |- *; try solve [reflexivity + inversion H].
  apply le_S_n_trans in H. eauto.
Defined.

Fixpoint nth_error_app2_trans {A} (l l' : list A) n:
  length l <= n ->
  nth_error (l ++ l') n = nth_error l' (n - length l).
Proof.
  intros.
  destruct l, n; cbn in H |- *; try solve [reflexivity + inversion H].
  apply le_S_n_trans in H. eauto.
Defined.


Fixpoint nth_error_map_trans {A B} (f : A -> B) n (l : list A):
  nth_error (map f l) n = option_map f (nth_error l n).
Proof. destruct l, n; try reflexivity. cbn; eauto.
Defined.

Fixpoint map_length_trans {A B} (f : A -> B) (l : list A):
  length (map f l) = length l.
Proof. destruct l; try reflexivity. cbn; eauto.
Defined.

Fixpoint nth_error_Some_trans {A} n x (l : list A):
  nth_error l n = Some x -> n < length l.
Proof.
  induction l, n; inversion 1; cbn.
  - auto with arith.
  - apply le_n_S_trans. unfold lt in *. eauto.
Defined.

Fixpoint nth_error_prod {A1 A2} (l1: list A1) (l2 : list A2) {struct l1}:
  forall n1 n2 x y,
  nth_error l1 n1 = Some x ->
  nth_error l2 n2 = Some y ->
  nth_error (list_prod l1 l2) (n1 * length l2 + n2) = Some (x,y).
Proof.
  intros n1 n2 x y H1 H2.
  induction l1 as [| a1 l1' IH], n1 in H1, H2, n1, n2 |- *;
  inversion H1; cbn.
  - rewrite nth_error_app1_trans.
    + rewrite nth_error_map_trans.
      rewrite H2.
      reflexivity.
    + rewrite map_length_trans.
      exact (nth_error_Some_trans _ y _ H2).
  - rewrite nth_error_app2_trans; rewrite map_length_trans.
    + rewrite add_schuffle_trans.
      rewrite add_sub_trans.
      eauto.
    + auto with arith.
Defined.

Inductive FiniteType_norec (T: Type) :=
  | finite_type_norec : FiniteType_norec T.

Fixpoint nth_error_app_l {A} (l l' : list A):
  forall n x,
    nth_error l n = Some x ->
    nth_error (l ++ l') n = Some x.
Proof.
  intros; erewrite nth_error_app1_trans.
  - assumption.
  - apply (nth_error_Some_trans _ x _). assumption.
Defined.

Fixpoint nth_error_app_r {A} (l l' : list A):
forall n x,
  nth_error l n = Some x ->
  nth_error (l' ++ l) (n + length l') = Some x.
Proof.
  intros; erewrite nth_error_app2_trans.
  - rewrite add_sub_trans. assumption.
  - auto with arith.
Defined.

Lemma nth_error_cons {A} (a : A) (l : list A):
forall x n,
  nth_error l n = Some x ->
  nth_error (a :: l) (S n) = Some x.
Proof. intros; simpl; assumption. Defined.

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
      rewrite (nth_error_map_trans (func1));
      let func2 := prod_function_rec (con) in
      unshelve erewrite func2;
      lazymatch goal with 
      | [|-  _ = _ ] => idtac
      | _ => shelve
      end;
      [> .. | simpl; reflexivity];
      lazymatch goal with
      | [ |- _ = Some ?z ] =>
        let tz := type of z in
        let tx := type of con in pose proof (finite_type_norec tx);
        eapply (finite_surjective (T := tz) (FiniteType := ltac:(typeclasses eauto)))
      end
    | _ =>
      instantiate (1 := 0);
      instantiate (1 := _ :: _);
      reflexivity
    end
  end.

Ltac FiniteType_t_nodup_increasing :=
  apply increasing_NoDup;
  vm_compute; reflexivity.

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
  Inductive t0 := A0 | B0. (* 1+1 = 2 instances *)
  Inductive t1 := A1 | B1 (x: t0) | C1. (* 1+2+1 = 4 instances *)
  Inductive t2 := A2 | B2 (x: t1) | C2 | D2 (x: t0). (* 1+4+1+2 = 8 instances *)
  Inductive t3 := A3 (x y: t2) (z: t1) | B3 (x y z: t0) | C3. (* 8*8*4 + 2*2*2 + 1 = 265 instances *)

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
