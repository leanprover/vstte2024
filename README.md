# Lean tutorial

**This material is still WIP.**

This is the accompanying code for the invited lean tutorial held at [VSTTE
2024](https://www.soundandcomplete.org/vstte2024.html) by Sebastian Ullrich and Joachim Breitner.

## Overview

In this tutorial we will see the following features of Lean

* basic functional programming
* extensible custom syntax for domain-specific functions
* inductive predicates and proofs 

The example use-case is a standard task in programming language theory: Embedding a small imperative
language, defining its semantics, and reasoning about it.

We won't have time to explain everything in complete detail, but we
hope that the overview we provide is a good starting point for
learning to use Lean. Please see [the documentation
section](https://lean-lang.org/documentation/) of the Lean website for
further resources. The [Lean Zulip](https://leanprover.zulipchat.com/)
is a friendly and helpful place to ask questions for both beginners
and experts.

## Preparing for the Tutorial

To prepare for the tutorial, please do the following:

1. [Install Lean](https://lean-lang.org/lean4/doc/quickstart.html)
2. Clone this repository
3. Ensure that you can build the code by running `lake build` from the
   command line
4. Ensure that your editor is correctly connected to Lean by opening
   one of the files, introducing an error, and checking that there is
   feedback

## Hands-on tasks

The tutorial will be in live-coding presentation style, with breaks for hands-on experiences. Here
are suggested tasks that you could try:

### First hands-on break

Suggested tasks, in rough order of difficulty.

* Add unary operations (negation, logical not) to the expression language.

* Let `Lean.Expr.optimize` apply rules like `0 + x = x`, `1 * x = x`.

  Hints:

  - It may be helpful to define a (non-recursive) function `Expr.optOp` with the same type as
    `Expr.op`, that serves as a “smart constructor”. Pattern matching can be elegant here!
  - In general it is advisible to write a separate theorem about each involved function
    (`BinOp.apply`, `Expr.optOp`, `Expr.optimize`) separately than to do it all in one go. 
    If these theorems are set up just right, they are good `@[simp]` lemmas, and will make the
    subsequent proof easy.

* Write a function `Expr.hasDiv : Expr → Bool` that checks if division is used in the expression.

  Prove that if an expression has no division, then `Expr.eval` will always return a result.

  Hint: There are various ways of phrasing this. You can use `Option.isSome` and write a theorem about
  `Option.bind` and `Option.isSome`. Or you can define `Expr.eval'` that returns `Value` (no
  `Option`) and prove that for expressions without division, the result of `Expr.eval` is
  `Option.some` of the value returned by `Expr.eval'`.

  Food for thought: How does this task relate to the previous task and the optimization `0 * x = 0`?
  If you have done both tasks, can you combine them?

  
### Second hands-on break

* Add nice input syntax for `Env.get σ "x"` and `Env.set`, e.g. `σ[x]` and `σ[x := e]` and update
  some of the proof statements.

* Add the optimization `x := x` to `Stmt.optimize`.

  Use `#guard_msgs` to check that it does what you want it to do on a small example.

  Finally, extend the verification proof.

  Hints:

  You may want to prove `@[simp] theorem set_get_same {σ : Env} : σ.set x (σ.get x) = σ` for that.
  To prove an equality on `Env`, add the `@[ext]` attribute to the `Env` structure. This will allow
  you to use `apply Env.ext` (or even start the proof with `ext y : 2` – check the docstring to see what that does.)

* (Short but tricky):

  Complete this proof that a looping program has no output
  ```lean
  def loop := imp {while (1) {skip;}}
  theorem infinite_loop : ¬ BigStep σ loop σ' := by
  ```
  
  Hint:

  Rephrase the statement so that the three arguments to `BigStep` are variables, so that `induction` works. You can do that using a helper theorem that you finally apply, or explore the `generalize` tactic.
 
## Code Structure

 - `Imp/Expr.lean` re-exports the expression language:
   - `Imp/Expr/Basic.lean` contains the AST of expressions
   - `Imp/Expr/Eval.lean` contains an evaluator for expressions
   - `Imp/Expr/Optimize.lean` contains a formally verified optimization pass
   - `Imp/Expr/Syntax.lean` adds a more convenient syntax for expressions
   - `Imp/Expr/Delab.lean` causes Lean to use the convenient syntax in
     its output (not part of tutorial, but nice to have!)
 - `Imp/Stmt.lean` re-exports the statement language:
   - `Imp/Stmt/Basic.lean` contains the AST and a convenient concrete
     syntax for statements
   - `Imp/Stmt/Delab.lean` causes Lean to use the convenient concrete
     syntax in its output (not part of tutorial, but nice to have!)
   - `Imp/Stmt/Optimize.lean` contains an optimization pass (unverified)
   - `Imp/Stmt/BigStep.lean` contains big-step operational semantics,
     and uses them to prove the optimizer correct. It also contains a
     function that implements these semantics, which can be used to
     run programs.
 - `Imp.lean` imports the other libraries, and contains a concluding
   demo of using a verified bit blaster to quickly prove theorems.

## Acknowledgments

This content is based on [material written by David Thrane
Christiansen](https://github.com/david-christiansen/lean-fkbh-24-2) for the tutorial "Lean for the
Functional Programmer", presented at *Mødegruppen for F#unktionelle Københavnere* by David Thrane
Christiansen on 2024-08-27 and 2024-09-24.

This material itself is based on a tutorial presented at [SSFT24](https://fm.csl.sri.com/SSFT24/) by
David Thrane Christiansen, co-developed with Leonardo de Moura.
