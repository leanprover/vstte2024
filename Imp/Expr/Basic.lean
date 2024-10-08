namespace Imp

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
  | op (op : BinOp) (e1 e2 : Expr)
deriving Repr, DecidableEq
