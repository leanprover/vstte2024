import Lean.PrettyPrinter.Parenthesizer
import Imp.Expr.Basic

namespace Imp.Expr

open Lean PrettyPrinter Parenthesizer


/- Add a new nonterminal to Lean's grammar, called `varname` -/
/-- Variable names in Imp -/
declare_syntax_cat varname

/- There are two productions: identifiers and antiquoted terms -/
syntax ident : varname
syntax:max "~" term:max : varname

/- `varname`s are included in terms using `var { ... }`, which is a hook on which to hang the macros
that translate the `varname` syntax into ordinary Lean expressions. -/
syntax "var " "{" varname "}" : term

/- These macros translate each production of the `varname` nonterminal into Lean expressions -/
macro_rules
  | `(var { $x:ident }) => `(term|$(quote x.getId.toString))
  | `(var { ~$stx }) => pure stx

/-- info: "x" : String -/
#guard_msgs in
#check var { x }

/-- info: "a lean" ++ "expr" : String -/
#guard_msgs in
#check var { ~("a lean" ++ "expr") }

/-- Expressions in Imp -/
declare_syntax_cat exp

/-- Variable names -/
syntax varname : exp

/-- Numeric constant -/
syntax num : exp

/-- Arithmetic complement -/
syntax:75 "-" exp:75 : exp

/-- Boolean negation -/
syntax:75 "!" exp:75 : exp

/-- Multiplication -/
syntax:70 exp:70 " * " exp:71 : exp
/-- Division -/
syntax:70 exp:70 " / " exp:71 : exp

/-- Addition -/
syntax:65 exp:65 " + " exp:66 : exp
/-- Subtraction -/
syntax:65 exp:65 " - " exp:66 : exp

/-- Left shift -/
syntax:55 exp:55 " <<< " exp:56 :exp
/-- Right shift -/
syntax:55 exp:55 " >>> " exp:56 :exp

/-- Less than -/
syntax:50 exp:50 " < " exp:51 : exp
/-- Less than or equal to -/
syntax:50 exp:50 " ≤ " exp:51 : exp
/-- Greater than or equal to -/
syntax:50 exp:50 " ≥ " exp:51 : exp
/-- Greater than -/
syntax:50 exp:50 " > " exp:51 : exp
/-- Equal -/
syntax:45 exp:45 " == " exp:46 : exp

/-- Bitwise and -/
syntax:40 exp:40 " &&& " exp:41 :exp
/-- Bitwise or -/
syntax:40 exp:40 " ||| " exp:41 :exp

/-- Boolean conjunction -/
syntax:35 exp:35 " && " exp:36 : exp
/-- Boolean disjunction -/
syntax:35 exp:35 " || " exp:36 : exp

/-- Parentheses for grouping -/
syntax "(" exp ")" : exp

/-- Escape to Lean -/
syntax:max "~" term:max : exp

/-- Embed an Imp expression into a Lean expression -/
syntax:min "expr " "{ " exp " }" : term

open Lean in
macro_rules
  | `(expr{$x:ident}) => `(Expr.var $(quote x.getId.toString))
  | `(expr{$n:num}) => `(Expr.const $(quote n.getNat))

  | `(expr{-$e}) => `(Expr.unop .neg (expr{$e}))
  | `(expr{!$e}) => `(Expr.unop .not (expr{$e}))

  | `(expr{$e1 + $e2}) => `(Expr.op .plus (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 * $e2}) => `(Expr.op .times (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 - $e2}) => `(Expr.op .minus (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 / $e2}) => `(Expr.op .div (expr{$e1}) (expr{$e2}))

  | `(expr{$e1 >>> $e2}) => `(Expr.op .rsh (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 <<< $e2}) => `(Expr.op .lsh (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ||| $e2}) => `(Expr.op .bor (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 &&& $e2}) => `(Expr.op .band (expr{$e1}) (expr{$e2}))


  | `(expr{$e1 && $e2}) => `(Expr.op .and (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 || $e2}) => `(Expr.op .or (expr{$e1}) (expr{$e2}))

  | `(expr{$e1 < $e2}) => `(Expr.op .lt (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ≤ $e2}) => `(Expr.op .le (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 == $e2}) => `(Expr.op .eq (expr{$e1}) (expr{$e2}))
  | `(expr{$e1 ≥ $e2}) => `(Expr.op .le (expr{$e2}) (expr{$e1}))
  | `(expr{$e1 > $e2}) => `(Expr.op .lt (expr{$e2}) (expr{$e1}))
  | `(expr{($e)}) => `(expr{$e})
  | `(expr{~$stx}) => pure stx

/-- info: op BinOp.plus («var» "x") (op BinOp.times («var» "y") («var» "z")) : Expr -/
#guard_msgs in
#check expr { x + y * z }


-- Copied from Lean's term parenthesizer - applies the precedence rules in the grammar to add
-- parentheses as needed. This isn't needed when adding new input syntax to Lean, but because the
-- file `Delab.lean` makes Lean use of this syntax in its output, the parentheses are needed.
@[category_parenthesizer exp]
def exp.parenthesizer : CategoryParenthesizer | prec => do
  maybeParenthesize `exp true wrapParens prec $
    parenthesizeCategoryCore `exp prec
where
  wrapParens (stx : Syntax) : Syntax := Unhygienic.run do
    let pstx ← `(($(⟨stx⟩)))
    return pstx.raw.setInfo (SourceInfo.fromRef stx)
