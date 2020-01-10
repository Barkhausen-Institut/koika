(*! Circuits | Syntax, semantics, compilation, and optimization of circuits !*)
Require Export Koika.Common Koika.Environments.
Require Import Koika.Syntax Koika.TypedSyntax Koika.TypedSyntaxTools.

Import PrimTyped CircuitSignatures.

Section Circuit.
  Context {rule_name_t reg_t ext_fn_t: Type}.
  Context {rwdata: nat -> Type}. (* Forward declaration *)

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Inductive rwdata_field :=
  | rwdata_r0
  | rwdata_r1
  | rwdata_w0
  | rwdata_w1
  | rwdata_data0
  | rwdata_data1.

  Inductive rwcircuit_field :=
  | rwcircuit_rwdata (r: reg_t) (field: rwdata_field)
  | rwcircuit_canfire.

  Inductive circuit: nat -> Type :=
  | CNot (c: circuit 1): circuit 1
  | CAnd (c1 c2: circuit 1): circuit 1
  | COr (c1 c2: circuit 1): circuit 1
  | CMux {sz} (select: circuit 1) (c1 c2: circuit sz): circuit sz
  | CConst {sz} (cst: bits sz): circuit sz
  | CReadRegister (reg: reg_t): circuit (CR reg)
  | CUnop (fn: fbits1) (a1: circuit (CSigma1 fn).(arg1Sig))
    : circuit (CSigma1 fn).(retSig)
  | CBinop (fn: fbits2) (a1: circuit (CSigma2 fn).(arg1Sig)) (a2: circuit (CSigma2 fn).(arg2Sig))
    : circuit (CSigma2 fn).(retSig)
  | CExternal (idx: ext_fn_t)
              (a: circuit (CSigma idx).(arg1Sig))
    : circuit (CSigma idx).(retSig)
  | CBundleRef {sz} (name: rule_name_t) (regs: list reg_t)
               (bundle: context (fun r => rwdata (CR r)) regs)
               (field: rwcircuit_field) (c: circuit sz): circuit sz
  | CAnnot {sz} (annot: string) (c: circuit sz): circuit sz.
End Circuit.

Arguments circuit {rule_name_t reg_t ext_fn_t rwdata} CR CSigma sz : assert.

Section Interpretation.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.
  Context {REnv: Env reg_t}.

  Context (cr: REnv.(env_t) (fun idx => bits (CR (idx)))).
  Context (csigma: forall f, CSig_denote (CSigma f)).

  Context {rwdata: nat -> Type}.
  Notation circuit := (@circuit rule_name_t reg_t ext_fn_t rwdata CR CSigma).

  Fixpoint interp_circuit {n} (c: circuit n) : bits n :=
    match c with
    | CNot c =>
      Ob~(negb (Bits.single (interp_circuit c)))
    | CAnd c1 c2 =>
      Ob~(andb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | COr c1 c2 =>
      Ob~(orb (Bits.single (interp_circuit c1)) (Bits.single (interp_circuit c2)))
    | CMux select c1 c2 =>
      if Bits.single (interp_circuit select) then interp_circuit c1
      else interp_circuit c2
    | CConst cst =>
      cst
    | CReadRegister idx =>
      REnv.(getenv) cr idx
    | CExternal fn arg =>
      csigma fn (interp_circuit arg)
    | CUnop fn arg1 =>
      PrimSpecs.sigma1 (Bits1 fn) (interp_circuit arg1)
    | CBinop fn arg1 arg2 =>
      PrimSpecs.sigma2 (Bits2 fn) (interp_circuit arg1) (interp_circuit arg2)
    | CBundleRef _ _ _ _ c =>
      interp_circuit c
    | CAnnot _ c =>
      interp_circuit c
    end.
End Interpretation.

Section CircuitOptimizer.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.

  Notation Circuit := circuit.
  Notation circuit := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).

  Context (csigma: forall f, CSig_denote (CSigma f)).

  Record local_circuit_optimizer :=
    { lco_fn :> forall {sz}, circuit sz -> circuit sz;
      lco_proof: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx))) {sz} (c: circuit sz),
          interp_circuit cr csigma (lco_fn c) =
          interp_circuit cr csigma c }.

  Definition lco_opt_compose
             (o1 o2: forall {sz}, circuit sz -> circuit sz) sz (c: circuit sz) :=
    o2 (o1 c).

  Definition lco_compose (l1 l2: local_circuit_optimizer) :=
    {| lco_fn := @lco_opt_compose (l1.(@lco_fn)) (l2.(@lco_fn));
       lco_proof := ltac:(abstract (intros; unfold lco_opt_compose;
                                     cbn; rewrite !lco_proof; reflexivity)) |}.

  Fixpoint unannot {sz} (c: circuit sz) : circuit sz :=
    match c with
    | CAnnot annot c => unannot c
    | c => c
    end.

  Lemma unannot_sound {REnv cr sz} :
    forall (c: circuit sz),
      interp_circuit (REnv := REnv) cr csigma (unannot c) =
      interp_circuit (REnv := REnv) cr csigma c.
  Proof. induction c; eauto. Qed.

  Section MuxElim.
    (** This pass performs the following Mux simplifications:
          Mux(_, c1, c1) → c1
          Mux(k, Mux(k', c2, c12), c2) → Mux(k && ~k', c12, c2 )
          Mux(k, Mux(k', c11, c2), c2) → Mux(k &&  k', c11, c2 )
          Mux(k, c1, Mux(k', c1, c22)) → Mux(k ||  k', c1 , c22)
          Mux(k, c1, Mux(k', c21, c1)) → Mux(k || ~k', c1 , c21)
          Mux(k, Mux(k, c11, c12), c2) → Mux(k, c11, c2)
          Mux(k, c1, Mux(k, c21, c22)) → Mux(k, c1, c22)
        [equivb] needs to be sound, but does not need to be complete
        (comparing two circuits can be very costly). **)
    Context (equivb: forall {sz}, circuit sz -> circuit sz -> bool).

    Context (equivb_sound: forall {REnv: Env reg_t} (cr: REnv.(env_t) (fun idx => bits (CR idx)))
                          {sz} (c1 c2: circuit sz),
                equivb _ c1 c2 = true ->
                interp_circuit cr csigma c1 = interp_circuit cr csigma c2).

    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Notation equivb_unannot c1 c2 := (equivb _ (unannot c1) (unannot c2)).

    Lemma equivb_unannot_sound :
      forall {sz} (c1 c2: circuit sz),
        equivb_unannot c1 c2 = true ->
        interp_circuit cr csigma c1 = interp_circuit cr csigma c2.
    Proof.
      intros * H%(equivb_sound _ cr).
      rewrite <- (unannot_sound c1), <- (unannot_sound c2); assumption.
    Qed.

    Definition opt_muxelim_identical {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c0 => if equivb_unannot c1 c2 then c1 else c0
      | _  => fun c0 => c0
      end c.

    Lemma opt_muxelim_identical_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_identical c) = interp_circuit cr csigma c.
    Proof.
      destruct c; simpl; try reflexivity.
      destruct equivb eqn:Hequivb.
      - destruct Bits.single; auto using equivb_unannot_sound.
      - reflexivity.
    Qed.

    Definition opt_muxelim_redundant_l {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot k k' then
                (* Mux(k, Mux(k, c11, c12), c2) *)
                (CAnnot "simplified_mux" (CMux k c11 c2))
              else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_redundant_r {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot k k' then
                (* Mux(k, c1, Mux(k, c21, c22)) *)
                (CAnnot "simplified_mux" (CMux k c1 c22))
              else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_l {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c1 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c11 c12 =>
            fun c c2 =>
              if equivb_unannot c11 c2 then
                (* Mux(k, Mux(k', c2, c12), c2) *)
                CMux (CAnnot "nested_mux" (CAnd k (CNot k'))) c12 c2
              else if equivb_unannot c12 c2 then
                     (* Mux(k, Mux(k', c11, c2), c2) *)
                     CMux (CAnnot "nested_mux" (CAnd k k')) c11 c2
                   else c
          | _ =>
            fun c c2 => c
          end c c2
      | _ => fun c => c
      end c.

    Definition opt_muxelim_nested_r {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | CMux k c1 c2 =>
        fun c =>
          match unannot c2 in Circuit _ _ sz return circuit sz -> circuit sz -> circuit sz with
          | CMux k' c21 c22 =>
            fun c c1 =>
              if equivb_unannot c1 c21 then
                (* Mux(k, c1, Mux(k', c1, c22)) *)
                CMux (CAnnot "nested_mux" (COr k k')) c1 c22
              else if equivb_unannot c1 c22 then
                     (* Mux(k, c1, Mux(k', c21, c1)) *)
                     CMux (CAnnot "nested_mux" (COr k (CNot k'))) c1 c21
                   else c
          | _ =>
            fun c c1 => c
          end c c1
      | _ => fun c => c
      end c.

    Ltac mux_elim_nested_step :=
      match goal with
      | _ => reflexivity
      | _ => congruence
      | _ => progress (intros || simpl)
      | [  |- context[match ?c with _ => _ end] ] =>
        match type of c with circuit _ => destruct c eqn:? end
      | [  |- context[if equivb_unannot ?c ?c' then _ else _] ] =>
        destruct (equivb_unannot c c') eqn:?
      | [ Heq: unannot ?c = _ |- context[interp_circuit _ _ ?c] ] =>
        rewrite <- (unannot_sound c), Heq
      | [  |- context[Bits.single ?c] ] =>
        destruct c as ([ | ] & []) eqn:?
      | [ H: equivb_unannot ?c ?c' = true |- _ ] => apply equivb_unannot_sound in H
      end.

    Lemma opt_muxelim_redundant_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_redundant_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_redundant_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_redundant_r; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_l_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_l c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_l; repeat mux_elim_nested_step.
    Qed.

    Lemma opt_muxelim_nested_r_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim_nested_r c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_muxelim_nested_r; repeat mux_elim_nested_step.
    Qed.

    Definition opt_muxelim {sz} :=
      @lco_opt_compose
        (@opt_muxelim_identical)
        (lco_opt_compose
           (lco_opt_compose (@opt_muxelim_redundant_l) (@opt_muxelim_redundant_r))
           (lco_opt_compose (@opt_muxelim_nested_l) (@opt_muxelim_nested_r)))
        sz.

    Lemma opt_muxelim_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_muxelim c) = interp_circuit cr csigma c.
    Proof.
      intros; unfold opt_muxelim, lco_opt_compose.
      rewrite
        opt_muxelim_nested_r_sound, opt_muxelim_nested_l_sound,
      opt_muxelim_redundant_r_sound, opt_muxelim_redundant_l_sound,
      opt_muxelim_identical_sound;
        reflexivity.
    Qed.
  End MuxElim.

  Section ConstProp.
    Context {REnv: Env reg_t}.
    Context (cr: REnv.(env_t) (fun idx => bits (CR idx))).

    Definition asconst {sz} (c: circuit sz) : option (list bool) :=
      match unannot c with
      | CConst cst => Some (vect_to_list cst)
      | c => None
      end.

    Notation ltrue := (cons true nil).
    Notation lfalse := (cons false nil).

    Instance EqDec_ListBool : EqDec (list bool) := _.

    Definition opt_constprop' {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz with
      | (CNot c) as c0 =>
        match asconst c with
        | Some ltrue => CConst Ob~0
        | Some lfalse => CConst Ob~1
        | _ => c0
        end
      | (CAnd c1 c2) as c0 =>
        match asconst c1, asconst c2 with
        | Some lfalse, _ | _, Some lfalse => CConst Ob~0
        | _, Some ltrue => c1
        | Some ltrue, _ => c2
        | _, _ => c0
        end
      | (COr c1 c2) as c0 =>
        match asconst c1, asconst c2 with
        | Some ltrue, _ | _, Some ltrue => CConst Ob~1
        | _, Some lfalse => c1
        | Some lfalse, _ => c2
        | _, _ => c0
        end
      | (CMux select c1 c2) as c0 =>
        match asconst select with
        | Some ltrue => c1
        | Some lfalse => c2
        | _ => match asconst c1, asconst c2 with
              | Some bs1, Some bs2 =>
                if eq_dec bs1 bs2 then c1
                else c0
              | _, _ => c0
              end
        end
      | c => c
      end.

    Definition opt_mux_bit1 {sz} (c: circuit sz): circuit sz :=
      match c in Circuit _ _ sz return circuit sz -> circuit sz with
      | @CMux _ _ _ _ _ _ n s c1 c2 =>
        fun c0 => match n return Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n -> Circuit _ _ n with
               | 1 => fun c0 c1 c2 =>
                       let annot := CAnnot "optimized_mux" in
                       match asconst c1, asconst c2 with
                       | Some ltrue, Some lfalse => annot s
                       | Some ltrue, _ => annot (COr s c2)
                       | Some lfalse, Some ltrue => annot (CNot s)
                       (* FIXME: these two increase the circuit size *)
                       (* | Some lfalse, _ => annot (CAnd (CNot s) c2) *)
                       (* | _, Some ltrue => annot (COr (CNot s) c1) *)
                       | _, Some lfalse => annot (CAnd s c1)
                       | _, _ => c0
                       end
               | _ => fun c0 c1 c2 => c0
               end c0 c1 c2
      | _ => fun c0 => c0
      end c.

    Definition opt_constprop {sz} (c: circuit sz): circuit sz :=
      match sz as n return (circuit n -> circuit n) with
      | 0 => fun c => CConst Bits.nil
      | _ => fun c => opt_mux_bit1 (opt_constprop' c)
      end c.

    Arguments opt_constprop sz !c : assert.

    Lemma asconst_Some :
      forall {sz} (c: circuit sz) bs,
        asconst c = Some bs ->
        vect_to_list (interp_circuit cr csigma c) = bs.
    Proof.
      induction c; intros b Heq;
        repeat match goal with
               | _ => progress cbn in *
               | _ => discriminate
               | _ => reflexivity
               | [ H: Some _ = Some _ |- _ ] => inversion H; subst; clear H
               | [ sz: nat |- _ ] => destruct sz; try (tauto || discriminate); []
               end.
      apply IHc; eassumption.
    Qed.

    Arguments EqDec_ListBool: simpl never.
    Lemma opt_constprop'_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop' c) = interp_circuit cr csigma c.
    Proof.
      induction c; cbn.
      Ltac t := match goal with
               | _ => reflexivity
               | _ => progress bool_simpl
               | _ => progress cbn in *
               | [  |- context[match asconst ?c with _ => _ end] ] =>
                 destruct (asconst c) as [ | ] eqn:?
               | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
               | [  |- _ = ?y ] =>
                 match y with
                 | context[Bits.single (interp_circuit cr csigma ?c)] =>
                   destruct (interp_circuit cr csigma c) as [ ? [] ] eqn:? ;
                   cbn in *; subst
                 end
               | [ H: ?x = _ |- context[?x] ] => rewrite H
               | [  |- context[if ?b then _ else _] ] => destruct b eqn:?
               | _ => eauto using vect_to_list_inj
               end.
      all: repeat t.
    Qed.

    Lemma opt_mux_bit1_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_mux_bit1 c) = interp_circuit cr csigma c.
    Proof.
      destruct c; simpl; try reflexivity; [].
      destruct sz as [ | [ | ] ]; simpl; try reflexivity; [].
      destruct (asconst c2) as [ [ | [ | ] [ | ] ] | ] eqn:Hc2; try reflexivity;
        destruct (asconst c3) as [ [ | [ | ] [ | ] ] | ] eqn:Hc3; try reflexivity.
      Ltac tmux :=
        match goal with
        | _ => progress (cbn in * || subst)
        | [ H: _ :: _ = _ :: _ |- _ ] => inversion H; subst; clear H
        | [ v: vect_nil_t _ |- _ ] => destruct v
        | [ H: asconst _ = Some _ |- _ ] => apply asconst_Some in H
        | [  |- context[interp_circuit _ _ ?c] ] => destruct (interp_circuit _ _ c) eqn:?
        | [  |- context[if ?x then _ else _] ] => destruct x
        | _ => reflexivity || discriminate
        end.
      all: solve [repeat tmux].
    Qed.

    Lemma opt_constprop_sound :
      forall {sz} (c: circuit sz),
        interp_circuit cr csigma (opt_constprop c) = interp_circuit cr csigma c.
    Proof.
      unfold opt_constprop; destruct sz.
      - cbn; intros.
        destruct interp_circuit; reflexivity.
      - intros; rewrite opt_mux_bit1_sound, opt_constprop'_sound; reflexivity.
    Qed.
  End ConstProp.
End CircuitOptimizer.

Arguments unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments unannot_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata} [sz] c : assert.
Arguments opt_constprop_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma [REnv] cr [sz] c : assert.

Arguments opt_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata} equivb [sz] c : assert.
Arguments opt_muxelim_sound {rule_name_t reg_t ext_fn_t CR CSigma rwdata} csigma {equivb} equivb_sound [REnv] cr [sz] c : assert.

Arguments lco_fn {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l [sz] c : assert.
Arguments lco_proof {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l {REnv} cr [sz] c : assert.
Arguments lco_compose {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} l1 l2 : assert.

Section LCO.
  Context {rule_name_t reg_t ext_fn_t: Type}.

  Context {CR: reg_t -> nat}.
  Context {CSigma: ext_fn_t -> CExternalSignature}.

  Context {rwdata: nat -> Type}.
  Context (csigma: forall f, CSig_denote (CSigma f)).

  Definition lco_unannot : @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := unannot;
       lco_proof := unannot_sound csigma |}.

  Definition lco_constprop: @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := opt_constprop;
       lco_proof := opt_constprop_sound csigma |}.

  Definition lco_muxelim equivb equivb_sound
    : @local_circuit_optimizer rule_name_t _ _ CR _ rwdata csigma :=
    {| lco_fn := opt_muxelim equivb;
       lco_proof := opt_muxelim_sound csigma equivb_sound |}.
End LCO.

Arguments lco_unannot {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_constprop {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} : assert.
Arguments lco_muxelim {rule_name_t reg_t ext_fn_t CR CSigma rwdata csigma} {equivb} equivb_sound : assert.

Section CircuitCompilation.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.

  Context {Show_var_t : Show var_t}.
  Context {Show_rule_name_t : Show rule_name_t}.

  Definition CR_of_R idx :=
    type_sz (R idx).
  Notation CR := CR_of_R.

  Definition CSigma_of_Sigma fn :=
    CSig_of_Sig (Sigma fn).
  Notation CSigma := CSigma_of_Sigma.

  Definition cr_of_r (r: REnv.(env_t) R)
    : REnv.(env_t) (fun idx => bits (CR idx)) :=
    map REnv (fun idx v => bits_of_value v) r.

  Definition csigma_of_sigma (sigma: forall f, Sig_denote (Sigma f))
    : forall f, CSig_denote (CSigma f) :=
    fun f => fun bs => bits_of_value (sigma f (value_of_bits bs)).

  Notation circuit' rwdata := (circuit (rule_name_t := rule_name_t) (rwdata := rwdata) CR CSigma).

  Inductive rwdata {sz: nat} :=
    { read0: circuit' (@rwdata) 1;
      read1: circuit' (@rwdata) 1;
      write0: circuit' (@rwdata) 1;
      write1: circuit' (@rwdata) 1;
      data0: circuit' (@rwdata) sz;
      data1: circuit' (@rwdata) sz }.
  Notation circuit := (circuit' (@rwdata)).

  Context (opt: forall {sz}, circuit sz -> circuit sz).
  Context (cr: REnv.(env_t) (fun reg => circuit (CR reg))).

  (* Notation CAnnot an c := (match an : string with _ => c end). *)
  Notation CAnnotOpt an c := (CAnnot an (opt _ c)).

  Declare Scope circuit.
  Notation "f [ arg ]` an `" :=
    (CAnnotOpt an (CExternal f arg (CConst Ob)))
      (at level 99, arg at level 99, format "f [ arg ]` an `") : circuit.
  Notation "f [ arg1 ',' arg2 ]` an `" :=
    (CAnnotOpt an (CExternal f arg1 arg2))
      (at level 99, arg1 at level 99, arg2 at level 99,
       format "f [ arg1 ','  arg2 ]` an `") : circuit.
  Notation "$` an ` c" :=
    (CAnnotOpt an (CConst c))
      (at level 75, format "$` an ` c") : circuit.
  Notation "!` an ` c" :=
    (CAnnotOpt an (CNot c))
      (at level 30, right associativity, format "!` an ` c") : circuit.
  Notation "c1 &&` an `  c2" :=
    (CAnnotOpt an (CAnd c1 c2))
      (at level 40, left associativity) : circuit.
  Notation "c1 ||` an `  c2" :=
    (CAnnotOpt an (COr c1 c2))
      (at level 50, left associativity) : circuit.
  Notation "c1 ==>` an ` c2" :=
    (CAnnotOpt an (COr (CAnnotOpt "impl" (CNot c1)) c2))
      (at level 70, no associativity) : circuit.
  Notation CMuxAnnotOpt an s c1 c2 :=
    (CAnnotOpt an (CMux s c1 c2)).

  Local Open Scope circuit.

  Definition readRegisters : forall idx: reg_t, circuit (CR idx) :=
    fun idx => CReadRegister (CR := CR) (CSigma := CSigma) idx.

  Definition rwset :=
    REnv.(env_t) (fun reg => @rwdata (CR reg)).

  Record rwcircuit :=
    { canFire: circuit 1;
      regs: rwset }.

  Record action_circuit {sz} :=
    { erwc: rwcircuit;
      retVal: circuit sz }.

  Definition scheduler_circuit :=
    rwset.

  Definition ccontext (sig: tsig var_t) :=
    context (fun '(k, tau) => circuit (type_sz tau)) sig.

  Definition mux_rwdata {sz} an (cond: circuit 1) (tReg fReg: @rwdata sz) :=
    {| read0 := CMuxAnnotOpt an cond (tReg.(read0)) (fReg.(read0));
       read1 := CMuxAnnotOpt an cond (tReg.(read1)) (fReg.(read1));
       write0 := CMuxAnnotOpt an cond (tReg.(write0)) (fReg.(write0));
       write1 := CMuxAnnotOpt an cond (tReg.(write1)) (fReg.(write1));
       data0 := CMuxAnnotOpt an cond (tReg.(data0)) (fReg.(data0));
       data1 := CMuxAnnotOpt an cond (data1 tReg) (data1 fReg) |}.

  Definition mux_rwsets an (cond: circuit 1) (tRegs fRegs: rwset) :=
    map2 REnv (fun k treg freg => mux_rwdata an cond treg freg)
                tRegs fRegs.

  Fixpoint mux_ccontext {sig} (cond: circuit 1) (ctxT: ccontext sig) (ctxF: ccontext sig) : ccontext sig.
    destruct sig as [ | (k, tau)]; cbn.
    - exact CtxEmpty.
    - apply (CtxCons (k, tau) (CMuxAnnotOpt "mux_ccontext" cond (chd ctxT) (chd ctxF))
                     (mux_ccontext _ cond (ctl ctxT) (ctl ctxF))).
  Defined.

  Section Action.
    Definition compile_unop (fn: fn1) (a: circuit (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig))):
      circuit (type_sz (PrimSignatures.Sigma1 fn).(retSig)) :=
      let cArg1 fn := circuit (type_sz (PrimSignatures.Sigma1 fn).(arg1Sig)) in
      let cRet fn := circuit (type_sz (PrimSignatures.Sigma1 fn).(retSig)) in
      match fn return cArg1 fn -> cRet fn with
      | Display fn => fun _ => CConst Ob
      | Conv tau fn => fun a =>
        match fn return cArg1 (Conv tau fn) -> cRet (Conv tau fn) with
        | Pack => fun a => a
        | Unpack => fun a => a
        | Ignore => fun _ => CConst Ob
        end a
      | Bits1 fn => fun a =>
        match fn return cArg1 (Bits1 fn) -> cRet (Bits1 fn) -> cRet (Bits1 fn) with
        | Not _ => fun a c => c
        | Repeat _ _ => fun a c => c
        | SExt sz width => fun a c =>
                            ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast, <- (Nat.mul_1_r (width - sz));
                                  exact (CBinop (Concat _ _)
                                                (CUnop (Repeat 1 (width - sz))
                                                       (CBinop (Sel sz) a (CConst (Bits.of_nat (log2 sz) (pred sz)))))
                                                a))
        | ZExtL sz width => fun a c =>
                             ltac:(subst cRet; simpl; rewrite <- vect_extend_end_cast;
                                     exact (CBinop (Concat _ _) (CConst Bits.zero) a))
        | ZExtR sz width => fun a c =>
                             ltac:(subst cRet; simpl; rewrite <- vect_extend_beginning_cast;
                                     exact (CBinop (Concat _ _) a (CConst Bits.zero)))
        | Slice sz offset width => fun a c => c
        end a (CUnop fn a)
      | Struct1 fn sig f => fun a =>
        match fn return cArg1 (Struct1 fn sig f) -> cRet (Struct1 fn sig f) with
        | GetField => fun a =>
          CUnop (GetFieldBits sig f) a
        end a
      | Array1 fn sig idx => fun a =>
        match fn return cArg1 (Array1 fn sig idx) -> cRet (Array1 fn sig idx) with
        | GetElement => fun a =>
          CUnop (GetElementBits sig idx) a
        end a
      end a.

    Definition compile_binop (fn: fn2)
               (a1: circuit (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)))
               (a2: circuit (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig))):
      circuit (type_sz (PrimSignatures.Sigma2 fn).(retSig)) :=
      let cArg1 fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(arg1Sig)) in
      let cArg2 fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(arg2Sig)) in
      let cRet fn := circuit (type_sz (PrimSignatures.Sigma2 fn).(retSig)) in
      match fn return cArg1 fn -> cArg2 fn -> cRet fn with
      | Eq tau negate => fun a1 a2 => CBinop (EqBits (type_sz tau) negate) a1 a2
      | Bits2 fn => fun a1 a2 => CBinop fn a1 a2
      | Struct2 fn sig f => fun a1 a2 =>
        match fn return cArg1 (Struct2 fn sig f) -> cArg2 (Struct2 fn sig f) -> cRet (Struct2 fn sig f) with
        | SubstField => fun a1 a2 =>
          CBinop (SubstFieldBits sig f) a1 a2
        end a1 a2
      | Array2 fn sig idx => fun a1 a2 =>
        match fn return cArg1 (Array2 fn sig idx) -> cArg2 (Array2 fn sig idx) -> cRet (Array2 fn sig idx) with
        | SubstElement => fun a1 a2 =>
          CBinop (SubstElementBits sig idx) a1 a2
        end a1 a2
      end a1 a2.

    Fixpoint compile_action
             {sig: tsig var_t}
             {tau}
             (Gamma: ccontext sig)
             (a: action pos_t var_t R Sigma sig tau)
             (clog: rwcircuit):
      @action_circuit (type_sz tau) * (ccontext sig) :=
      match a in action _ _ _ _ ts tau return ccontext ts -> @action_circuit (type_sz tau) * ccontext ts with
      | Fail tau => fun Gamma =>
        ({| retVal := $`"fail"`Bits.zeroes (type_sz tau); (* LATER: Question mark here *)
            erwc := {| canFire := $`"fail_cF"` Ob~0;
                       regs := clog.(regs) |} |},
         Gamma)
      | @Var _ _ _ _ _ _ _ k _ m => fun Gamma =>
        ({| retVal := CAnnotOpt (String.append "var_" (show k)) (cassoc m Gamma);
            erwc := clog |},
         Gamma)
      | Const cst => fun Gamma =>
        ({| retVal := CAnnotOpt "constant_value_from_source" (CConst (bits_of_value cst));
           erwc := clog |},
         Gamma)
      | Seq r1 r2 => fun Gamma =>
        let (cex, Gamma) := (compile_action Gamma r1 clog) in
        compile_action Gamma r2 cex.(erwc)
      | @Assign _ _ _ _ _ _ _ k tau m ex => fun Gamma =>
        let (cex, Gamma) := compile_action Gamma ex clog in
        ({| retVal := $`"assign_retVal"`Bits.nil;
            erwc := cex.(erwc) |},
         creplace m cex.(retVal) Gamma)
      | @Bind _ _ _ _ _ _ sig tau tau' var ex body => fun Gamma =>
        let (ex, Gamma) := compile_action Gamma ex clog in
        let (ex, Gamma) := compile_action (CtxCons (var, tau) ex.(retVal) Gamma) body ex.(erwc) in
        (ex, ctl Gamma)
      | If cond tbranch fbranch => fun Gamma =>
        let (cond, Gamma) := compile_action Gamma cond clog in
        let (tbranch, Gamma_t) := compile_action Gamma tbranch cond.(erwc) in
        let (fbranch, Gamma_f) := compile_action Gamma fbranch cond.(erwc) in
        ({| retVal := CMuxAnnotOpt "if_retVal" cond.(retVal) tbranch.(retVal) fbranch.(retVal);
           erwc := {| canFire := CMuxAnnotOpt "if_cF" cond.(retVal) tbranch.(erwc).(canFire) fbranch.(erwc).(canFire);
                     regs := mux_rwsets "if_mux" cond.(retVal) tbranch.(erwc).(regs) fbranch.(erwc).(regs) |} |},
         mux_ccontext cond.(retVal) Gamma_t Gamma_f)
      | Read P0 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := CAnnotOpt "read0" (REnv.(getenv) cr idx);
           erwc := {| canFire := clog.(canFire);
                     regs := REnv.(putenv) clog.(regs) idx {| read0 := $`"read0"` Ob~1;
                                                             (* Unchanged *)
                                                             read1 := reg.(read1);
                                                             write0 := reg.(write0);
                                                             write1 := reg.(write1);
                                                             data0 := reg.(data0);
                                                             data1 := reg.(data1) |} |} |},
         Gamma)
      | Read P1 idx => fun Gamma =>
        let reg := REnv.(getenv) clog.(regs) idx in
        ({| retVal := reg.(data0);
            erwc := {| canFire := clog.(canFire);
                      regs := REnv.(putenv) clog.(regs) idx {| read1 := $`"read1"` Ob~1;
                                                              (* Unchanged *)
                                                              read0 := reg.(read0);
                                                              write0 := reg.(write0);
                                                              write1 := reg.(write1);
                                                              data0 := reg.(data0);
                                                              data1 := reg.(data1) |} |} |},
         Gamma)
      | Write P0 idx val => fun Gamma =>
        let (val, Gamma) := compile_action Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        ({| retVal := $`"write_retVal"`Bits.nil;
            erwc := {| canFire := (val.(erwc).(canFire) &&`"write0_cF"`
                                 (!`"no_read1"` reg.(read1) &&`"write0_cF"`
                                  !`"no_write0"` reg.(write0) &&`"write0_cF"`
                                  !`"no_write1"` reg.(write1)));
                      regs := REnv.(putenv) val.(erwc).(regs) idx {| write0 := $`"write0"` (Ob~1);
                                                                    data0 := val.(retVal);
                                                                    (* Unchanged *)
                                                                    read0 := reg.(read0);
                                                                    read1 := reg.(read1);
                                                                    write1 := reg.(write1);
                                                                    data1 := reg.(data1) |} |} |},
         Gamma)
      | Write P1 idx val => fun Gamma =>
        let (val, Gamma) := compile_action Gamma val clog in
        let reg := REnv.(getenv) val.(erwc).(regs) idx in
        ({| retVal := $`"write_retVal"`Bits.nil;
            erwc := {| canFire := val.(erwc).(canFire) &&`"write1_cF"` !`"no_write1"` reg.(write1);
                      regs := REnv.(putenv) val.(erwc).(regs) idx {| write1 := $`"write1"` (Ob~1);
                                                                    data1 := val.(retVal);
                                                                    (* Unchanged *)
                                                                    read0 := reg.(read0);
                                                                    read1 := reg.(read1);
                                                                    write0 := reg.(write0);
                                                                    data0 := reg.(data0) |} |} |},
         Gamma)
      | Unop fn a => fun Gamma =>
        let (a, Gamma) := compile_action Gamma a clog in
        ({| retVal := compile_unop fn a.(retVal);
            erwc := a.(erwc) |},
         Gamma)
      | Binop fn a1 a2 => fun Gamma =>
        let (a1, Gamma) := compile_action Gamma a1 clog in
        let (a2, Gamma) := compile_action Gamma a2 a1.(erwc) in
        ({| retVal := compile_binop fn a1.(retVal) a2.(retVal);
            erwc := a2.(erwc) |},
         Gamma)
      | ExternalCall fn a => fun Gamma =>
        let (a, Gamma) := compile_action Gamma a clog in
        ({| retVal := CAnnotOpt "External_call" (CExternal fn a.(retVal));
            erwc := a.(erwc) |},
         Gamma)
      | APos _ a => fun Gamma =>
        compile_action Gamma a clog
      end Gamma.
  End Action.

  Definition adapter (cs: scheduler_circuit) : rwcircuit :=
    {| canFire := $`"cF_init"` Ob~1;
       regs := map REnv (fun k reg => {| read0 := $`"init_no_read0"` Ob~0;
                                       read1 := $`"init_no_read1"` Ob~0;
                                       write0 := $`"init_no_write0"` Ob~0;
                                       write1 := $`"init_no_write1"` Ob~0;
                                       data0 := reg.(data0);
                                       data1 := reg.(data1) |})
                         cs |}.

  Definition willFire_of_canFire'_read0 {sz} (ruleReg inReg: @rwdata sz) :=
    (ruleReg.(read0)) ==>`"read0_wF_of_cF"`
    (!`"read0_wF_no_writes"` ((inReg.(write0)) ||`""` (inReg.(write1)))).

  Definition willFire_of_canFire'_write0 {sz} (ruleReg inReg: @rwdata sz) :=
    (ruleReg.(write0)) ==>`"write0_wF_of_cF"`
    (!`"write0_wF_no_writes_no_read1"`
       ((inReg.(write0)) ||`""` (inReg.(write1)) ||`""` (inReg.(read1)))).

  Definition willFire_of_canFire'_rw1 {sz} (ruleReg inReg: @rwdata sz) :=
    ((ruleReg.(read1)) ||`""` (ruleReg.(write1))) ==>`"read_write1_wF_of_cF"`
    (!`"read_write1_wF_no_write1"` (inReg.(write1))).

  Definition willFire_of_canFire' {sz} (ruleReg inReg: @rwdata sz) :=
    (willFire_of_canFire'_read0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_write0 ruleReg inReg) &&`""`
    (willFire_of_canFire'_rw1 ruleReg inReg).

  Definition willFire_of_canFire rl_name cRule cInput : circuit 1 :=
    let annot := String.append "wF_" (show rl_name) in
    fold_right REnv
           (fun k '(ruleReg, inReg) acc =>
              acc &&`annot` willFire_of_canFire' ruleReg inReg)
           (zip REnv cRule.(regs) cInput) cRule.(canFire).

  Arguments willFire_of_canFire' : simpl never.

  Definition update_accumulated_rwset (rl_rwset acc: rwset) :=
    let an := "compute_accumulated_rwset" in
    map2 REnv (fun _ ruleReg accReg =>
                   {| read0 := (ruleReg.(read0)) ||`an` (accReg.(read0));
                      read1 := (ruleReg.(read1)) ||`an` (accReg.(read1));
                      write0 := (ruleReg.(write0)) ||`an` (accReg.(write0));
                      write1 := (ruleReg.(write1)) ||`an` (accReg.(write1));
                      data0 := (ruleReg.(data0));
                      data1 := (ruleReg.(data1)) |})
                rl_rwset acc.

  Definition bundleref_wrap_rwdata rl rs bundle (r: reg_t) (ruleReg: @rwdata (CR r))
    : @rwdata (CR r) :=
    let ft := REnv.(finite_keys) in
    if List.find (fun r' => beq_dec (EQ := EqDec_FiniteType) r r') rs then
      {| read0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_r0) (ruleReg.(read0));
         read1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_r1) (ruleReg.(read1));
         write0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_w0) (ruleReg.(write0));
         write1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_w1) (ruleReg.(write1));
         data0 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_data0) (ruleReg.(data0));
         data1 := CBundleRef rl rs bundle (rwcircuit_rwdata r rwdata_data1) (ruleReg.(data1)) |}
    else ruleReg.

  Definition bundleref_wrap_rwset rl rs bundle (rws: rwset) :=
    map REnv (bundleref_wrap_rwdata rl rs bundle) rws.

  Definition bundleref_wrap_erwc rl rs bundle erwc :=
    {| canFire := CBundleRef rl rs bundle rwcircuit_canfire erwc.(canFire);
       regs := bundleref_wrap_rwset rl rs bundle erwc.(regs) |}.

  Definition bundleref_wrap_action_circuit
             {tau} (rs: list reg_t)
             (input: rwset) (rl: @action_circuit tau) (rl_name: rule_name_t)
    : @action_circuit tau :=
    let bundle := ccreate rs (fun r _ => REnv.(getenv) input r) in
    {| erwc := bundleref_wrap_erwc rl_name rs bundle rl.(erwc);
       retVal := rl.(retVal) |}.

  Context (rules: rule_name_t -> rule pos_t var_t R Sigma).
  Context (external: rule_name_t -> bool).

  Fixpoint compile_scheduler_circuit
           (s: scheduler pos_t rule_name_t)
           (input: scheduler_circuit):
    scheduler_circuit :=
    let compile_action rl_name :=
      let rule := rules rl_name in
      let ft := REnv.(finite_keys) in
      let rs := action_registers (EQ := EqDec_FiniteType) rule in
      let (rl, _) := compile_action CtxEmpty rule (adapter input) in
      let rl := if external rl_name then bundleref_wrap_action_circuit rs input rl rl_name else rl in
      let acc := update_accumulated_rwset rl.(erwc).(regs) input in
      (rl, acc) in
    match s with
    | Done =>
      input
    | Cons rl_name s =>
      let (rl, acc) := compile_action rl_name in
      let will_fire := willFire_of_canFire rl_name rl.(erwc) input in
      let input := mux_rwsets "mux_input" will_fire acc input in
      compile_scheduler_circuit s input
    | Try rl_name st sf =>
      let (rl, acc) := compile_action rl_name in
      let st := compile_scheduler_circuit st acc in
      let sf := compile_scheduler_circuit sf input in
      let will_fire := willFire_of_canFire rl_name rl.(erwc) input in
      mux_rwsets "mux_subschedulers" will_fire st sf
    | SPos _ s =>
      compile_scheduler_circuit s input
    end.

  Definition commit_rwdata {sz} (reg: @rwdata sz) : circuit sz :=
    CMuxAnnotOpt "commit_write1" (reg.(write1)) (reg.(data1)) (reg.(data0)).

  Definition init_scheduler_rwdata idx : rwdata :=
    {| read0 := $`"sched_init_no_read0"` Ob~0;
       read1 := $`"sched_init_no_read1"` Ob~0;
       write0 := $`"sched_init_no_write0"` Ob~0;
       write1 := $`"sched_init_no_write1"` Ob~0;
       data0 := CAnnotOpt "sched_init_data0_is_reg" (REnv.(getenv) cr idx);
       data1 := CAnnotOpt "sched_init_no_data1" (CConst Bits.zero) |}.

  Definition init_scheduler_circuit : scheduler_circuit :=
    REnv.(create) init_scheduler_rwdata.

  Definition register_update_circuitry :=
    REnv.(env_t) (fun reg => circuit (CR reg)).

  Definition compile_scheduler' (s: scheduler pos_t rule_name_t)
    : register_update_circuitry :=
    let s := compile_scheduler_circuit s init_scheduler_circuit in
    map REnv (fun k r => commit_rwdata r) s.
End CircuitCompilation.

Arguments CR_of_R {reg_t} R idx : assert.
Arguments CSigma_of_Sigma {ext_fn_t} Sigma fn : assert.
Arguments cr_of_r {reg_t} {R} {REnv} r : assert.
Arguments csigma_of_sigma {ext_fn_t} {Sigma} sigma f a : assert.

Arguments readRegisters {rule_name_t reg_t ext_fn_t} R Sigma idx : assert.
Arguments rwdata {rule_name_t reg_t ext_fn_t} R Sigma sz : assert.
Arguments action_circuit {rule_name_t reg_t ext_fn_t} R Sigma REnv sz : assert.
Arguments scheduler_circuit {rule_name_t reg_t ext_fn_t} R Sigma REnv : assert.
Arguments register_update_circuitry rule_name_t {reg_t ext_fn_t} R Sigma REnv : assert.

Section Helpers.
  Context {pos_t var_t rule_name_t reg_t ext_fn_t: Type}.

  Context {R: reg_t -> type}.
  Context {Sigma: ext_fn_t -> ExternalSignature}.
  Context {FiniteType_reg_t: FiniteType reg_t}.

  Context {Show_var_t: Show var_t}.
  Context {Show_rule_name_t: Show rule_name_t}.

  Notation circuit :=
    (circuit (rule_name_t := rule_name_t)
             (rwdata := rwdata (rule_name_t := rule_name_t) R Sigma)
             (CR_of_R R) (CSigma_of_Sigma Sigma)).
  Context (opt: forall {sz}, circuit sz -> circuit sz).

  Definition compile_scheduler
             (rules: rule_name_t -> rule pos_t var_t R Sigma)
             (external: rule_name_t -> bool)
             (s: scheduler pos_t rule_name_t)
    : register_update_circuitry rule_name_t R Sigma _ :=
    let cr := ContextEnv.(create) (readRegisters R Sigma) in
    compile_scheduler' opt cr rules external s.

  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sig_denote (Sigma f)).

  Definition interp_circuits
             (circuits: register_update_circuitry rule_name_t R Sigma REnv) :=
    let cr := cr_of_r r in
    let csigma := csigma_of_sigma sigma in
    map REnv (fun _ c => interp_circuit cr csigma c) circuits.
End Helpers.