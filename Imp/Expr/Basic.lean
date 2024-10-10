namespace Imp

inductive UnOp where
  | neg | not
deriving Repr, DecidableEq

/-- Binary operators -/
inductive BinOp where
  | plus | minus | times | div
  | lsh | rsh
  | band | bor
  | and | or
  | lt | le | eq
deriving Repr, DecidableEq

/-- Expressions -/
inductive Expr where
  | const (i : BitVec 32)
  | var (name : String)
  | unop (op : UnOp) (e : Expr)
  | op (op : BinOp) (e1 e2 : Expr)
deriving Repr, DecidableEq

/-- info: Expr.op BinOp.plus (Expr.const 23) (Expr.const 42) : Expr -/
#guard_msgs in
#check Expr.op BinOp.plus (Expr.const 23) (Expr.const 42)

/-- info: Expr.op BinOp.plus (Expr.const 23) (Expr.const 42) : Expr -/
#guard_msgs in
#check Expr.op .plus (.const 23) (.const 42)
