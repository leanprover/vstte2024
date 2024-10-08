import Imp.Expr

import Imp.Stmt.Delab
import Imp.Stmt.Optimize

namespace Imp

namespace Stmt

/--
Big-step semantics: `BigStep σ s σ'` means that running the program `s` in the starting state `σ` is
termination with the final state `σ'`.
-/
inductive BigStep : Env → Stmt → Env → Prop where
  | skip :
    BigStep σ (imp {skip;}) σ
  | seq :
    BigStep σ s1 σ' → BigStep σ' s2 σ'' →
    BigStep σ (imp{ ~s1 ~s2}) σ''
  | assign :
    e.eval σ = some v →
    BigStep σ (imp {~x := ~e;}) (σ.set x v)
  | ifTrue :
    c.eval σ = some v →
    v ≠ 0 →
    BigStep σ s1 σ' →
    BigStep σ (imp {if (~c) {~s1} else {~s2}}) σ'
  | ifFalse :
    c.eval σ = some 0 →
    BigStep σ s2 σ' →
    BigStep σ (imp {if (~c) {~s1} else {~s2}}) σ'
  | whileTrue :
    c.eval σ = some v →
    v ≠ 0 →
    BigStep σ body σ' →
    BigStep σ' (imp {while (~c) {~body}}) σ'' →
    BigStep σ (imp {while (~c) {~body}}) σ''
  | whileFalse :
    c.eval σ = some 0 →
    BigStep σ (imp {while (~c) {~body}}) σ

attribute [simp] BigStep.skip


@[simp]
theorem BigStep.skip_pre_eq_post : BigStep σ (imp {skip;}) σ' ↔ (σ = σ') := by
  constructor
  . intro .skip; rfl
  . intro heq; simp [heq]





/--
`swap` terminates, and the resulting environment contains swapped inputs.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by
  unfold swap
  apply Exists.intro
  constructor
  . apply BigStep.seq
    . apply BigStep.assign
      simp [Expr.eval, Env.get, Env.set]
      rfl
    . apply BigStep.seq
      . apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
      . simp
        apply BigStep.assign
        simp [Expr.eval, Env.get, Env.set]
        rfl
  . simp [Env.get, Env.set]

/--
`swap` terminates, and the resulting environment contains swapped inputs. This proof is shorter.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by
  repeat' constructor

/--
`swap` terminates, and the resulting environment contains swapped inputs. This version works no
matter what the input values are.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) swap σ' ∧ σ'.get "x" = y ∧ σ'.get "y" = x  := by
  repeat' constructor


/--
`min` computes the minimum of its inputs.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" x |>.set "y" y) min σ' ∧ if x < y then σ'.get "min" = x else σ'.get "min" = y := by
  -- This takes the “wrong path” at if:
  -- repeat' constructor
  -- simp
  unfold min
  by_cases h : x < y
  . apply Exists.intro; constructor
    . apply BigStep.ifTrue
      . simp [Expr.eval, BinOp.apply, Env.get, Env.set, *]
        rfl
      . simp
      . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
    . simp [Env.get, Env.set]
      bv_omega
  . apply Exists.intro; constructor
    . apply BigStep.ifFalse
      . simp [Expr.eval, BinOp.apply, Env.get, Env.set, *]
      . constructor; simp [Expr.eval, Env.get, Env.set]; rfl
    . simp [Env.get, Env.set]
      intro; contradiction

def loop := imp {while (1) {skip;}}

/--
`loop` is really an infinite loop - there is no final state that it can result in.
-/
theorem infinite_loop : ¬ BigStep σ loop σ' := by
  generalize h' : loop = l
  intro h
  induction h <;> try (simp [loop, *] at *; done)
  case whileTrue ih =>
    exact ih h'
  case whileFalse σ c body cFalse =>
    have : c = (expr { 1 }) := by simp_all [loop]
    simp [Expr.eval, this] at cFalse

/-- Optimizing a program doesn't change its meaning -/
theorem optimize_ok : BigStep σ s σ' → BigStep σ s.optimize σ' := by
  intro h
  induction h with simp only [optimize]
  | «skip» => constructor
  | seq s1 s2 ih1 ih2 =>
    split
    next eq2 =>
      rw [eq2] at ih1
      cases ih1; apply ih2
    next eq1 eq2 =>
      rw [eq1] at ih2
      cases ih2; apply ih1
    next =>
      apply BigStep.seq ih1 ih2
  | assign m =>
    constructor
    rw [← Expr.optimize_ok]
    assumption
  | ifTrue ceq hnn l ih =>
    split
    next isFalse =>
      exfalso
      rw [Expr.optimize_ok, isFalse] at ceq
      simp [Expr.eval] at ceq
      simp [ceq] at hnn
    next notFalse _isConst =>
      apply ih
    next =>
      split
      . assumption
      . apply BigStep.ifTrue
        . rw [← Expr.optimize_ok]
          assumption
        · assumption
        . assumption
  | ifFalse isFalse l ih =>
    split
    next =>
      apply ih
    next nonZero isConst =>
      rw [Expr.optimize_ok, isConst] at isFalse
      simp [Expr.eval] at isFalse
      contradiction
    next =>
      split
      . simp [*]
      . apply BigStep.ifFalse
        . rw [← Expr.optimize_ok]
          assumption
        . assumption
  | whileFalse =>
    split <;> try simp
    apply BigStep.whileFalse
    rw [← Expr.optimize_ok]
    assumption
  | whileTrue isTrue hnn bodyStep nextStep ih1 ih2 =>
    split
    next c isZero =>
      rw [Expr.optimize_ok, isZero] at isTrue
      simp [Expr.eval] at isTrue
      subst isTrue
      contradiction
    next c isNotZero =>
      apply BigStep.whileTrue
      . rw [← Expr.optimize_ok, isTrue]
      · assumption
      . apply ih1
      . simp [optimize] at ih2
        assumption

/--
Run a program, with the number of loop iterations limited by the `Nat` parameter. Returns `none`
if the program doesn't terminate fast enough or if some other problem means the result is undefined
(e.g. division by zero).
 -/
def run (σ : Env) (s : Stmt) (n : Nat) : Option Env :=
  match s with
  | imp {skip;} =>
    some σ
  | imp {~s1 ~s2} => do
    let σ' ← run σ s1 n
    run σ' s2 n
  | imp {~x := ~e;} => do
    let v ← e.eval σ
    pure (σ.set x v)
  | imp {if (~c) {~s1} else {~s2}} => do
    let v ← c.eval σ
    if v = 0 then
      run σ s2 n
    else
      run σ s1 n
  | imp {while (~c) {~s1}} => do
    let n + 1 := n
      | none
    let v ← c.eval σ
    if v = 0 then
      pure σ
    else
      let σ' ← run σ s1 n
      run σ' (imp {while (~c) {~s1}}) n

/-- Helper lemma for the next proof -/
theorem bind_eq_some : (Option.bind x f = some y) ↔ (∃ a, x = some a ∧ f a = some y) := by
  constructor
  . simp [Option.bind]
    intro eq
    split at eq
    next => simp at eq
    next =>
      simp [*]
  . intro ⟨a, x_is_some, f_is_some⟩
    simp [*]

/--
`run` is correct: if it returns an answer, then that final state can be reached by the big-step
semantics. This is not total correctness - `run` could always return `none` - but it does increase
confidence.
-/
theorem run_some_implies_big_step : run σ s n = some σ' → BigStep σ s σ' := by
  intro term
  induction σ, s, n using run.induct generalizing σ' <;> simp_all [run, bind_eq_some]
  case case2 σ n s1 s2 ih1 ih2 =>
    let ⟨σ'', run_s1, run_s2⟩ := term
    -- Right nesting needed to run the first `trivial` before the second `apply_assumption`, which solves a metavariable
    constructor <;> (apply_assumption <;> trivial)
  case case3 =>
    let ⟨v, has_val, next_env⟩ := term
    subst_eqs
    constructor <;> trivial
  case case4 ih1 ih2 =>
    let ⟨v, has_val, next_env⟩ := term
    split at next_env
    · apply BigStep.ifFalse <;> simp_all
    · apply BigStep.ifTrue (v := v) <;> simp_all
  case case5 ih1 ih2 =>
    let ⟨v, has_val, next_env⟩ := term
    split at next_env
    . simp_all [BigStep.whileFalse]
    . simp [bind_eq_some] at next_env
      let ⟨σ'', run_s1_eq, run_while_eq⟩ := next_env
      apply BigStep.whileTrue (v := v)
      . simp [*]
      · assumption
      . exact ih1 run_s1_eq
      . exact ih2 _ run_while_eq

theorem run_some_more_fuel (h : n ≤ m) : run σ s n = some σ' → run σ s m = some σ' := by
  induction σ, s, n using run.induct generalizing σ' m
  all_goals simp_all [run, bind_eq_some]
  case case2 ih1 ih2 =>
    intros σ'' s1 s2
    apply Exists.intro σ''
    constructor
    · exact ih1 h s1
    · exact ih2 σ'' h s2
  case case4 ih1 ih2 =>
    intro x _
    split <;> (intro; simp_all)
  case case5 ih1 ih2 =>
    cases m
    case zero => simp at h
    case succ m =>
      simp at h
      simp (config := {contextual:= true}) [run, bind_eq_some]
      intro x _
      split
      · simp
      · simp [bind_eq_some]
        intro x s1 s2
        apply Exists.intro x
        constructor
        · apply ih1 h s1
        · apply ih2 _ h s2

theorem big_step_implies_run_some (h : BigStep σ s σ') : ∃ n, run σ s n = some σ':= by
  induction h
  all_goals try solve | simp_all [run]
  case «seq» ih1 ih2 =>
    let ⟨n1, ih1⟩ := ih1
    let ⟨n2, ih2⟩ := ih2
    apply Exists.intro (max n1 n2)
    rw [run]
    rw [run_some_more_fuel (by omega) ih1]
    rw [Option.bind_eq_bind, Option.some_bind]
    rw [run_some_more_fuel (by omega) ih2]
  case «whileTrue» v σ''' body σ' c σ'' hc hnn _ _ ih1 ih2 =>
    let ⟨n1, ih1⟩ := ih1
    let ⟨n2, ih2⟩ := ih2
    apply Exists.intro (max n1 n2 + 1)
    simp [run, hc]
    split
    · contradiction
    · rw [run_some_more_fuel (by omega) ih1]
      simp
      rw [run_some_more_fuel (by omega) ih2]
  case «whileFalse» h =>
    apply Exists.intro 1
    simp [run, h]
