import Lean.PrettyPrinter.Delaborator
import Std.Tactic.BVDecide

import Imp.Expr
import Imp.Stmt

namespace Imp.Stmt

/-
The final demo - read this file last!
-/

/--
popcount implementation from Hacker's Delight, Second Edition, by Henry S. Warren, Jr.
Figure 5-2 on p. 82.
-/
def popcount : Stmt := imp {
  x := x - ((x >>> 1) &&& 0x55555555);
  x := (x &&& 0x33333333) + ((x >>> 2) &&& 0x33333333);
  x := (x + (x >>> 4)) &&& 0x0F0F0F0F;
  x := x + (x >>> 8);
  x := x + (x >>> 16);
  x := x &&& 0x0000003F;
}


def pop_spec (x : BitVec 32) : BitVec 32 :=
  go x 0 32
where
  go (x : BitVec 32) (pop : BitVec 32) (i : Nat) : BitVec 32 :=
    match i with
    | 0 => pop
    | i + 1 =>
      let pop := pop + (x &&& 1#32)
      go (x >>> 1#32) pop i

def test_popcount (x : BitVec 32) : Bool :=
  run (Env.init x) popcount 2024 |>.map (·.get "x" == pop_spec x) |>.getD false

/-- info: true -/
#guard_msgs in
#eval test_popcount 0
/-- info: true -/
#guard_msgs in
#eval test_popcount 1
/-- info: true -/
#guard_msgs in
#eval test_popcount 55
/-- info: true -/
#guard_msgs in
#eval test_popcount 129837


theorem popCount_correct : test_popcount x := by
  simp! [test_popcount, popcount, pop_spec, Stmt.run]
  bv_decide
