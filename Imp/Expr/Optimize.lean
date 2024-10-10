import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .unop uop e =>
    match optimize e with
    | .const i =>
      if let some v := uop.apply i then .const v
      else .unop uop (.const i)
    | e' => .unop uop e'
  | .op bop e1 e2 =>
    match optimize e1, optimize e2 with
    | .const i, .const i' =>
      if let some v := bop.apply i i' then .const v
      else .op bop (.const i) (.const i')
    | .const 0, e2' =>
      if bop = .plus then e2' else .op bop (.const 0) e2'
    | e1', e2' =>
        .op bop e1' e2'

@[simp]
theorem BinOp.apply_plus_0 (v : Value) :  BinOp.plus.apply (0#32) v = v  :=
  by simp [BinOp.apply]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e <;> simp [optimize]
  case unop uop e ih =>
    split <;> simp [eval, *]
    split
    · simp [eval, *]
    · simp [eval]
  case op bop e1 e2 ih1 ih2 =>
    split <;> simp [eval, *]
    · split
      · simp [eval, *]
      · simp [eval]
    · split
      · simp [eval, *]
      · simp [eval, *]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e using optimize.induct <;> simp [optimize, eval, *]
