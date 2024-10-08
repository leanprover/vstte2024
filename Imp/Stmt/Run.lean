import Imp.Stmt.BigStep

namespace Imp

namespace Stmt

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

/-- info: 3628800 -/
#guard_msgs in
#eval ((run (Env.init 0 |>.set "n" 10) fact 100).get!.get "out").toNat

example : run σ (imp {skip;}) n = some σ := by
  simp [run]

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
