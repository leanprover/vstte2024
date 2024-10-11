import Imp.Expr.Basic

open Lean

namespace Imp

/-- Values stored in memory - 32-bit integers -/
abbrev Value := BitVec 32

/-- An environment maps variables names to their values (no pointers) -/
@[ext]
structure Env where
  get : String → Value
deriving Inhabited

namespace Env

/-- Initialize an environment, setting all uninitialized memory to `i` -/
def init (i : Value) : Env where
  get _ := i

/-- Set a value in an environment -/
def set (x : String) (v : Value) (σ : Env) : Env where
  get y := if x == y then v else σ.get y

/-
Using `syntax` and `macro_rules` as seen:

syntax term noWs "[[" term "]]" : term
syntax term noWs "[[" term " := " term "]]" : term
macro_rules | `($e[[ $x ]]) => `(Env.get $e $x)
macro_rules | `($e[[ $x := $v ]]) => `(Env.set $x $v $e)

But we can also use `notation` which is a bit more limited, but automatically defines
a delaboration, so we get pretty goals!
-/

notation σ "[[" x "]]" => Env.get σ x
notation σ "[[" x " := " v "]]" => Env.set x v σ

@[simp]
theorem get_init : (Env.init v)[[x]] = v := by rfl

@[simp]
theorem get_set_same {σ : Env} : σ[[ x := v ]][[x]] = v := by
  simp [get, set]

@[simp]
theorem get_set_different {σ : Env} : x ≠ y →  σ[[ x := v ]][[y]] = σ[[ y ]] := by
  intros
  simp [get, set, *]

@[simp]
theorem set_get_same {σ : Env} : σ[[ x := σ[[x]] ]] = σ := by
  ext x : 2
  simp [get, set]
  intro h
  simp [*]


end Env

/-- Helper that implements unary operators -/
def UnOp.apply : UnOp → Value → Option Value
  | .neg, x => some (- x)
  | .not, x => some (if x == 0 then 1 else 0)

/-- Helper that implements binary operators -/
def BinOp.apply : BinOp → Value → Value → Option Value
  | .plus, x, y => x + y
  | .minus, x, y => x - y
  | .times, x, y => x * y
  | .lsh, x, y => x <<< y
  | .rsh, x, y => x >>> y
  | .band, x, y => x &&& y
  | .bor, x, y => x ||| y
  | .div, _, 0 => none
  | .div, x, y => x / y
  | .and, 0, _ => some 0
  | .and, _, y => y
  | .or, 0, y => y
  | .or, x, _ => x
  | .eq, x, y => some (if x == y then 1 else 0)
  | .le, x, y => some (if x ≤ y then 1 else 0)
  | .lt, x, y => some (if x < y then 1 else 0)

/--
Evaluates an expression, finding the value if it has one.

Expressions that divide by zero don't have values - the result is undefined.
-/
def Expr.eval (σ : Env) : Expr → Option Value
  | .const i => i
  | .var x => σ[[x]]
  | .unop uop e => do
    let v ← e.eval σ
    uop.apply v
  | .op bop e1 e2 => do
    let v1 ← e1.eval σ
    let v2 ← e2.eval σ
    bop.apply v1 v2

/-- Whether an expression contains the div operator (and thus could fail) -/
def Expr.hasNoDiv : Expr → Bool
  | .const _ => true
  | .var _ => true
  | .unop _ e => e.hasNoDiv
  | .op .div _ _ => false
  | .op _ e1 e2 => e1.hasNoDiv && e2.hasNoDiv

inductive Expr.HasNoDiv : Expr → Prop where
  | const : Expr.HasNoDiv (.const i)
  | var : Expr.HasNoDiv (.var i)
  | unop : HasNoDiv e → Expr.HasNoDiv (.unop uop e)
  | bop : HasNoDiv e1 → HasNoDiv e2 → bop ≠ .div → Expr.HasNoDiv (.op bop e1 e2)

theorem Option.bind_isSome_of_isSome_of_forall_isSome {f : α → Option β}
    (h1 : o.isSome) (h2 : ∀ x, (f x).isSome) : (Option.bind o f).isSome := by
  cases o
  · contradiction
  · simp [*]

@[simp]
theorem UnOp.apply_isSome (uop : UnOp) (v : Value) : (uop.apply v).isSome := by
  unfold UnOp.apply
  split <;> simp [*]

@[simp]
theorem BinOp.apply_isSome (bop : BinOp) (v₁ v₂ : Value) (h : bop ≠ .div) : (bop.apply v₁ v₂).isSome := by
  unfold BinOp.apply
  split <;> simp [*]
  contradiction

theorem Expr.eval_isSome_of_hasDiv (e : Expr) (h : e.hasNoDiv) : (e.eval σ).isSome := by
  induction e using hasNoDiv.induct
  case case1 => simp [eval]
  case case2 => simp [eval]
  case case3 =>
    simp [hasNoDiv] at h
    simp [eval]
    apply Option.bind_isSome_of_isSome_of_forall_isSome
    · simp [*]
    · simp [*]
  case case4 =>
    simp [hasNoDiv] at h
  case case5 bop _ _ h_not_div _ _ =>
    simp [hasNoDiv, *] at h
    have : bop ≠ .div := by cases bop <;> trivial
    obtain ⟨h₁ , h₂⟩ := h
    simp [eval]
    apply Option.bind_isSome_of_isSome_of_forall_isSome
    · simp [*]
    · intro v
      apply Option.bind_isSome_of_isSome_of_forall_isSome
      · simp [*]
      · simp [*]
