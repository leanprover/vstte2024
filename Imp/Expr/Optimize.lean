import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

def optOp : BinOp → Expr → Expr → Expr
  | bop, .const i, .const i' =>
    if let some v := bop.apply i i' then .const v
    else .op bop (.const i) (.const i')
  | .plus, .const 0, e2 => e2
  | bop, e1, e2 => .op bop e1 e2

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
    .optOp bop e1.optimize e2.optimize

@[simp]
theorem BinOp.apply_plus_0 (v : Value) :  BinOp.plus.apply (0#32) v = v  :=
  by simp [BinOp.apply]

@[simp]
theorem optOp_ok (bop : BinOp) (e1 e2 : Expr) : (optOp bop e1 e2).eval σ = (op bop e1 e2).eval σ  := by
  unfold optOp
  split
  · split
    · simp [eval, *]
    · simp [eval, *]
  · simp [eval, *]
  · simp [eval, *]

theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e
  case unop uop e ih =>
    unfold optimize
    split <;> simp [eval, *]
    split
    · simp [eval, *]
    · simp [eval]
  case op bop e1 e2 ih1 ih2 =>
    unfold optimize
    simp [eval, *]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e using optimize.induct <;> simp [optimize, eval, *]
