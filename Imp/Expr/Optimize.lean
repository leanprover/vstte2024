import Imp.Expr.Basic
import Imp.Expr.Eval

namespace Imp.Expr

/-- Smart constructor that optimizes unary operations. NB: Same type as `Expr.unop` -/
def unopOpt : UnOp → Expr → Expr
  | uop, .const i =>
    if let some v := uop.apply i then .const v
    else .unop uop (.const i)
  | uop, e => .unop uop e

/-- Smart constructor that optimizes binary operations. NB: Same type as `Expr.op` -/
def opOpt : BinOp → Expr → Expr → Expr
  | bop, .const i, .const i' =>
    if let some v := bop.apply i i' then .const v
    else .op bop (.const i) (.const i')
  | .plus, .const 0, e => e
  | .plus, e, const 0 => e
  | .times, .const 1, e => e
  | .times, e, const 1 => e
  | bop, e1, e2 => .op bop e1 e2

/--
Optimizes an expression by folding constants.
-/
def optimize : Expr → Expr
  | .const i => .const i
  | .var x => .var x
  | .unop uop e => .unopOpt uop (optimize e)
  | .op bop e1 e2 => .opOpt bop (optimize e1) (optimize e2)

/-- Correctness of the `.unOpt` smart constructor -/
@[simp]
theorem unopOpt_ok : (Expr.unopOpt uop e).eval σ = (Expr.unop uop e).eval σ := by
  unfold Expr.unopOpt
  split <;> simp [eval, *]
  · split <;> simp [eval, *]

@[simp] theorem BinOp.apply_plus_0_left  : BinOp.plus.apply (0#32) v = v := by simp [BinOp.apply]
@[simp] theorem BinOp.apply_plus_0_right : BinOp.plus.apply v (0#32) = v := by simp [BinOp.apply]
@[simp] theorem BinOp.apply_mul_1_left   : BinOp.times.apply (1#32) v = v := by simp [BinOp.apply]
@[simp] theorem BinOp.apply_mul_1_right  : BinOp.times.apply v (1#32) = v := by simp [BinOp.apply]

/-- Correctness of the `.opOpt` smart constructor -/
@[simp]
theorem opOpt_ok : (Expr.opOpt bop e1 e2).eval σ = (Expr.op bop e1 e2).eval σ := by
  unfold Expr.opOpt
  split <;> simp [eval, *]
  · split <;> simp [eval, *]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e <;> simp [optimize, eval, *]

/--
Optimization doesn't change the meaning of any expression
-/
theorem optimize_ok' (e : Expr) : e.eval σ = e.optimize.eval σ := by
  induction e using optimize.induct <;> simp [optimize, eval, *]
