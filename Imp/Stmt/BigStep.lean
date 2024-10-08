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

/--
A first simple theorem: `skip` doesn't change the state.
-/
@[simp]
theorem BigStep.skip_pre_eq_post : BigStep σ (imp {skip;}) σ' ↔ (σ = σ') := by
  constructor
  . intro .skip; rfl
  . intro heq; simp [heq, BigStep.skip]

/--
`swap` terminates, and the resulting environment contains swapped inputs.
-/
example : ∃σ', BigStep (Env.init 0 |>.set "x" 5 |>.set "y" 22) swap σ' ∧ σ'.get "x" = 22 ∧ σ'.get "y" = 5 := by
  unfold swap
  apply Exists.intro -- introduces ?w for the witness
  constructor
  . apply BigStep.seq
    . apply BigStep.assign
      simp [Expr.eval]
      rfl
    . apply BigStep.seq
      . apply BigStep.assign
        simp [Expr.eval]
        rfl
      . apply BigStep.assign
        simp [Expr.eval]
        rfl
  . simp

/--
`swap` terminates, and the resulting environment contains swapped inputs. This proof is shorter.
(NB: `rfl` is a `constructor` of sorts, and the `simp` above aren't really needed.)
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
      . simp [Expr.eval, BinOp.apply, *]
        rfl
      . simp
      . apply BigStep.assign
        simp [Expr.eval]
        rfl
    . simp
      bv_omega
  . apply Exists.intro; constructor
    . apply BigStep.ifFalse
      . simp [Expr.eval, BinOp.apply, *]
      . constructor
        simp [Expr.eval]
        rfl
    . simp
      bv_omega

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
