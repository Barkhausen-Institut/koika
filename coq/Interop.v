Require Import Koika.Common Koika.Environments Koika.Types Koika.TypedSyntax Koika.Circuits.
Require Export Koika.Primitives.

Inductive empty_ext_fn_t :=.
Definition empty_Sigma (fn: empty_ext_fn_t)
  : ExternalSignature := match fn with end.
Definition empty_sigma fn
  : Sig_denote (empty_Sigma fn) := match fn with end.
Definition empty_CSigma (fn: empty_ext_fn_t)
  : CExternalSignature := CSigma_of_Sigma empty_Sigma fn.
Definition empty_csigma fn
  : CSig_denote (empty_CSigma fn) := csigma_of_sigma empty_sigma fn.
Definition empty_fn_names (fn: empty_ext_fn_t)
  : string := match fn with end.

Section Packages.
  (** [pos_t]: The type of positions used in actions.
      Typically [string] or [unit]. *)
  Context {pos_t: Type}.

  (** [var_t]: The type of variables used in let bindings.
      Typically [string]. *)
  Context {var_t: Type}.

  (** [rule_name_t]: The type of rule names.
      Typically an inductive [rule1 | rule2 | …]. **)
  Context {rule_name_t: Type}.

  (** [reg_t]: The type of registers used in the program.
      Typically an inductive [R0 | R1 | …] *)
  Context {reg_t: Type}.

  (** [ext_fn_t]: The type of external functions names.
      Typically an inductive. *)
  Context {ext_fn_t: Type}.

  Record koika_package_t :=
    {
      (** [koika_reg_names]: These names are used to generate readable code. *)
      koika_reg_names: Show reg_t;
      (** [koika_reg_types]: The type of data stored in each register. *)
      koika_reg_types: reg_t -> type;
      (** [koika_reg_init]: The initial value stored in each register. *)
      koika_reg_init: forall r: reg_t, koika_reg_types r;
      (** [koika_reg_finite]: We need to be able to enumerate the set of registers
          that the program uses. *)
      koika_reg_finite: FiniteType reg_t;

      (** [koika_ext_fn_types]: The signature of each function. *)
      koika_ext_fn_types: forall fn: ext_fn_t, ExternalSignature;

      (** [koika_rules]: The rules of the program. **)
      koika_rules: forall _: rule_name_t,
          TypedSyntax.rule pos_t var_t koika_reg_types koika_ext_fn_types;
      (** [koika_rule_names]: These names are used to generate readable code. **)
      koika_rule_names: Show rule_name_t;

      (** [koika_scheduler]: The scheduler. **)
      koika_scheduler: TypedSyntax.scheduler pos_t rule_name_t;

      (** [koika_module_name]: The name of the current package. **)
      koika_module_name: string
    }.

  Record circuit_package_t :=
    {
      cp_pkg: koika_package_t;

      (** [cp_reg_env]: This describes how the program concretely stores maps
        keyed by registers (this is used in the type of [cp_circuits], which is
        essentially a list of circuits, one per register. *)
      cp_reg_Env: Env reg_t;

      (** [cp_circuits]: The actual circuitry generated by the
        compiler (really a list of circuits, one per register). *)
      cp_circuits: @register_update_circuitry
                    rule_name_t reg_t ext_fn_t
                    (cp_pkg.(koika_reg_types)) (cp_pkg.(koika_ext_fn_types))
                    cp_reg_Env;
    }.

  Record verilog_package_t :=
    {
      (** [vp_ext_fn_names]: A map from custom function names to Verilog
          function names. *)
      vp_ext_fn_names: forall fn: ext_fn_t, string;

      (** [vp_external_rules]: A list of rule names to be replaced with
          Verilog implementations *)
      vp_external_rules: list rule_name_t
    }.

  Record sim_package_t :=
    {
      (** [sp_var_names]: These names are used to generate readable code. *)
      sp_var_names: Show var_t;

      (** [sp_ext_fn_names]: A map from custom function names to C++ function
          names. *)
      sp_ext_fn_names: forall fn: ext_fn_t, string;

      (** [sp_extfuns]: A piece of C++ code implementing the custom external
          functions used by the program.  This is only needed if [ext_fn_t] is
          non-empty.  It should implement a class called 'extfuns', with public
          functions named consistently with [sp_ext_fn_names] **)
      sp_extfuns: option string
    }.
End Packages.

Section TypeConv.
  Fixpoint struct_to_list {A} (f: forall tau: type, type_denote tau -> A)
           (fields: list (string * type)) (v: struct_denote fields): list (string * A) :=
    match fields return struct_denote fields -> list (string * A) with
    | [] => fun v => []
    | (nm, tau) :: fields => fun v => (nm, f tau (fst v)) :: struct_to_list f fields (snd v)
    end v.

  Definition struct_of_list_fn_t A :=
    forall a: A, { tau: type & type_denote tau }.

  Definition struct_of_list_fields {A} (f: struct_of_list_fn_t A) (aa: list (string * A)) :=
    List.map (fun a => (fst a, projT1 (f (snd a)))) aa.

  Fixpoint struct_of_list {A} (f: struct_of_list_fn_t A) (aa: list (string * A))
    : struct_denote (struct_of_list_fields f aa) :=
    match aa with
    | [] => tt
    | a :: aa => (projT2 (f (snd a)), struct_of_list f aa)
    end.

  Lemma struct_of_list_to_list {A}
        (f_ls: forall tau: type, type_denote tau -> A)
        (f_sl: struct_of_list_fn_t A) :
    (forall a, f_ls (projT1 (f_sl a)) (projT2 (f_sl a)) = a) ->
    (* (forall a, f_ls (projT1 (f_sl a)) = a) -> *)
    forall (aa: list (string * A)),
      struct_to_list f_ls _ (struct_of_list f_sl aa) = aa.
  Proof.
    induction aa; cbn.
    - reflexivity.
    - setoid_rewrite IHaa. rewrite H; destruct a; reflexivity.
  Qed.

  Fixpoint struct_to_list_of_list_cast {A}
        (f_ls: forall tau: type, type_denote tau -> A)
        (f_sl: struct_of_list_fn_t A)
        (pr: forall tau a, projT1 (f_sl (f_ls tau a)) = tau)
        (fields: list (string * type)) (v: struct_denote fields) {struct fields}:
    struct_of_list_fields f_sl (struct_to_list f_ls fields v) = fields.
  Proof.
    destruct fields as [| (nm, tau) fields]; cbn.
    - reflexivity.
    - unfold struct_of_list_fields in *;
        rewrite struct_to_list_of_list_cast by eauto.
      rewrite pr; reflexivity.
  Defined.

  Lemma struct_to_list_of_list {A}
        (f_ls: forall tau: type, type_denote tau -> A)
        (f_sl: struct_of_list_fn_t A)
        (fields: list (string * type))
        (pr: forall tau a, f_sl (f_ls tau a) = existT _ tau a):
    forall (v: struct_denote fields),
      (struct_of_list f_sl (struct_to_list f_ls _ v)) =
      ltac:(rewrite struct_to_list_of_list_cast by (intros; rewrite pr; eauto); exact v).
  Proof.
    induction fields as [| (nm, tau) fields]; cbn; destruct v; cbn in *.
    - reflexivity.
    - rewrite IHfields; clear IHfields.
      unfold eq_ind_r, eq_ind, eq_sym.
      set (struct_to_list_of_list_cast _ _ _ _ _) as Hcast; clearbody Hcast.
      change (fold_right _ _ ?fields) with (struct_denote fields) in *.
      set (struct_to_list f_ls fields f) as sfs in *; clearbody sfs;
        destruct Hcast; cbn.
      set (pr _ _) as pr'; clearbody pr'.
      set ((f_sl (f_ls tau t))) as a in *; clearbody a.
      set (struct_of_list_fields f_sl sfs) as ssfs in *.
      destruct a; cbn; inversion pr'; subst.
      apply Eqdep_dec.inj_pair2_eq_dec in H1; try apply eq_dec; subst.
      setoid_rewrite <- Eqdep_dec.eq_rect_eq_dec; try apply eq_dec.
      reflexivity.
  Qed.
End TypeConv.

Section Compilation.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Definition compile_koika_package
             (s: @koika_package_t pos_t var_t rule_name_t reg_t ext_fn_t)
             (opt: let circuit sz := circuit (CR_of_R s.(koika_reg_types))
                                            (CSigma_of_Sigma s.(koika_ext_fn_types)) sz in
                   forall {sz}, circuit sz -> circuit sz)
    : circuit_package_t :=
    let _ := s.(koika_reg_finite) in
    {| cp_circuits := compile_scheduler opt s.(koika_rules) s.(koika_scheduler) |}.
End Compilation.

Record interop_package_t :=
  { pos_t := unit;
    var_t := string;
    ip_reg_t : Type;
    ip_rule_name_t : Type;
    ip_ext_fn_t : Type;
    ip_koika : @koika_package_t pos_t var_t ip_rule_name_t ip_reg_t ip_ext_fn_t;
    ip_verilog : @verilog_package_t ip_rule_name_t ip_ext_fn_t;
    ip_sim : @sim_package_t var_t ip_ext_fn_t }.

Require Import Koika.ExtractionSetup.

Module Backends.
  Section Backends.
    Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.
    Notation koika_package_t := (@koika_package_t pos_t var_t rule_name_t reg_t ext_fn_t).
    Notation verilog_package_t := (@verilog_package_t rule_name_t ext_fn_t).
    Notation sim_package_t := (@sim_package_t var_t ext_fn_t).

    Axiom compile_circuits: koika_package_t -> verilog_package_t -> unit.
    Axiom compile_simulation: koika_package_t -> sim_package_t -> unit.
    Axiom compile_all: interop_package_t -> unit.
    Axiom register: interop_package_t -> unit.
  End Backends.

  Extract Constant compile_circuits =>
  "fun kp vp -> Koika.Interop.compile_circuits (Obj.magic kp) (Obj.magic vp)".
  Extract Constant compile_simulation =>
  "fun kp sp -> Koika.Interop.compile_simulation (Obj.magic kp) (Obj.magic vp)".
  Extract Constant compile_all =>
  "fun ip -> Koika.Interop.compile_all (Obj.magic ip)".
  Extract Constant register =>
  "fun ip -> Registry.register (Obj.magic ip)".
End Backends.
