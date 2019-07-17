Require Import Coq.Lists.List.
Require Export SGA.Common SGA.Environments SGA.Syntax SGA.TypedSyntax.

Import ListNotations.

Section Logs.
  Inductive LogEntryKind :=
    LogRead | LogWrite.

  Record LogEntry {T} :=
    LE { kind: LogEntryKind;
         port: Port;
         val: match kind with
              | LogRead => unit: Type
              | LogWrite => T
              end }.

  Definition RLog T :=
    list (@LogEntry T).

  Context {reg_t: Type}.
  Context {R: reg_t -> type}.
  Context {REnv: Env reg_t}.
  Definition Log := REnv.(env_t) (fun idx => RLog (R idx)).

  Definition log_empty : Log :=
    REnv.(create) (fun _ => []).

  Definition log_app (l1 l2: Log) :=
    REnv.(map2) (fun _ ll1 ll2 => ll1 ++ ll2) l1 l2.

  Fixpoint list_find_opt {A B} (f: A -> option B) (l: list A) : option B :=
    match l with
    | [] => None
    | x :: l =>
      let fx := f x in
      match fx with
      | Some y => Some y
      | None => list_find_opt f l
      end
    end.

  Lemma list_find_opt_app {A B} (f: A -> option B) (l l': list A) :
    list_find_opt f (l ++ l') =
    match list_find_opt f l with
    | Some x => Some x
    | None => list_find_opt f l'
    end.
  Proof.
    induction l; cbn; intros.
    - reflexivity.
    - rewrite IHl. destruct (f a); reflexivity.
  Qed.

  Definition log_find {T} (log: Log) reg (f: @LogEntry (R reg) -> option T) : option T :=
    list_find_opt f (REnv.(getenv) log reg).

  Lemma log_find_app {T} (l l': Log) reg (f: @LogEntry (R reg) -> option T) :
    log_find (log_app l l') reg f =
    match log_find l reg f with
    | Some x => Some x
    | None => log_find l' reg f
    end.
  Proof.
    unfold log_find, log_app, map2.
    rewrite getenv_create.
    rewrite list_find_opt_app.
    reflexivity.
  Qed.

  Definition log_forallb (log: Log) reg (f: LogEntryKind -> Port -> bool) :=
    List.forallb (fun '(LE _ kind prt _) => f kind prt) (REnv.(getenv) log reg).

  Definition log_cons (reg: reg_t) le (l: Log) :=
    REnv.(putenv) l reg (le :: REnv.(getenv) l reg).
End Logs.

Arguments LE {_}.
Arguments LogEntry: clear implicits.
Arguments RLog: clear implicits.
Arguments Log {reg_t} R REnv.

Section Interp.
  Context {var_t reg_t fn_t: Type}.
  Context {reg_t_eq_dec: EqDec reg_t}.

  Context {R: reg_t -> type}.
  Context {Sigma: fn_t -> ExternalSignature}.
  Context {REnv: Env reg_t}.
  Context (r: REnv.(env_t) R).
  Context (sigma: forall f, Sigma f).
  Open Scope bool_scope.

  Notation Log := (Log R REnv).

  Definition may_read0 (sched_log rule_log: Log) idx :=
    (log_forallb sched_log idx
                 (fun kind prt => match kind, prt with
                               | LogWrite, P0 => false
                               | _, _ => true
                               end)) &&
    (log_forallb (log_app rule_log sched_log) idx
                 (fun kind prt => match kind, prt with
                               | LogWrite, P1 => false
                               | _, _ => true
                               end)).

  Definition may_read1 (sched_log: Log) idx :=
    log_forallb sched_log idx
                (fun kind prt => match kind, prt with
                              | LogWrite, P1 => false
                              | _, _ => true
                              end).

  Definition latest_write0 (log: Log) idx :=
    log_find log idx
             (fun le => match le with
                     | (LE LogWrite P0 v) => Some v
                     | _ => None
                     end).

  Definition may_write (sched_log rule_log: Log) prt idx :=
    match prt with
    | P0 => log_forallb (log_app rule_log sched_log) idx
                       (fun kind prt => match kind, prt with
                                     | LogRead, P1 | LogWrite, _ => false
                                     | _, _ => true
                                     end)
    | P1 => log_forallb (log_app rule_log sched_log) idx
                       (fun kind prt => match kind, prt with
                                     | LogWrite, P1 => false
                                     | _, _ => true
                                     end)
    end.

  Notation expr := (expr var_t R Sigma).
  Notation rule := (rule var_t R Sigma).
  Notation scheduler := (scheduler var_t R Sigma).

  Definition vcontext (sig: tsig var_t) :=
    context (fun '(k, tau) => Type_of_type tau) sig.

  Section Expr.
    Context {sig: tsig var_t}.
    Context (Gamma: vcontext sig).
    Context (sched_log: Log).

    Fixpoint interp_expr {tau}
             (rule_log: Log)
             (e: expr sig tau)
      : option (Log * tau) :=
      match e with
      | Var m =>
        Some (rule_log, cassoc m Gamma)
      | Const cst => Some (rule_log, cst)
      | Read P0 idx =>
        if may_read0 sched_log rule_log idx then
          Some (log_cons idx (LE LogRead P0 tt) rule_log, REnv.(getenv) r idx)
        else None
      | Read P1 idx =>
        if may_read1 sched_log idx then
          Some (log_cons idx (LE LogRead P1 tt) rule_log,
                match latest_write0 (log_app rule_log sched_log) idx with
                | Some v => v
                | None => REnv.(getenv) r idx
                end)
        else None
      | Call fn arg1 arg2 =>
        let/opt2 rule_log, arg1 := interp_expr rule_log arg1 in
        let/opt2 rule_log, arg2 := interp_expr rule_log arg2 in
        Some (rule_log, (sigma fn) arg1 arg2)
      end.
  End Expr.

  Section Rule.
    Fixpoint interp_rule
             {sig: tsig var_t}
             (Gamma: vcontext sig)
             (sched_log: Log)
             (rule_log: Log)
             (rl: rule sig)
    : option Log :=
      match rl in TypedSyntax.rule _ _ _ t return (vcontext t -> option Log) with
      | Skip => fun _ => Some rule_log
      | Fail => fun _ => None
      | Seq r1 r2 =>
        fun Gamma =>
          let/opt rule_log := interp_rule Gamma sched_log rule_log r1 in
          interp_rule Gamma sched_log rule_log r2
      | @Bind _ _ _ _ _ _ tau var ex body =>
        fun Gamma =>
          let/opt2 rule_log, v := interp_expr Gamma sched_log rule_log ex in
          interp_rule (CtxCons (var, tau) v Gamma) sched_log rule_log body
      | If cond tbranch fbranch =>
        fun Gamma =>
        let/opt2 rule_log, cond := interp_expr Gamma sched_log rule_log cond in
        if bits_single cond then
          interp_rule Gamma sched_log rule_log tbranch
        else
          interp_rule Gamma sched_log rule_log fbranch
      | Write prt idx val =>
        fun Gamma =>
          let/opt2 rule_log, val := interp_expr Gamma sched_log rule_log val in
          if may_write sched_log rule_log prt idx then
            Some (log_cons idx (LE LogWrite prt val) rule_log)
          else None
      end Gamma.
  End Rule.

  Section Scheduler.
    Fixpoint interp_scheduler'
             (sched_log: Log)
             (s: scheduler)
             {struct s} :=
      match s with
      | Done => sched_log
      | Try r s1 s2 =>
        match interp_rule CtxEmpty sched_log log_empty r with
        | Some l => interp_scheduler' (log_app l sched_log) s1
        | CannotRun => interp_scheduler' sched_log s2
        end
      end.

    Definition interp_scheduler (s: scheduler) :=
      interp_scheduler' log_empty s.
  End Scheduler.
End Interp.
