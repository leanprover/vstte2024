# Lean for Functional Programmers

This is the accompanying code for "Lean for the Functional
Programmer", a tutorial presented at *Mødegruppen for F#unktionelle
Københavnere* by David Thrane Christiansen on 2024-08-27 and
2024-09-24.

## Overview

This tutorial has two parts: an introduction to programming and
proving in Lean, and a demonstration of using Lean to embed a small
imperative language and reason about its semantics. This repository
contains code for the second of the two.

This tutorial is aimed at introducing Lean's language embedding
features, with a tutorial focused on formalization rather than
programming. In particular, this tutorial demonstrates formalizing the
semantics of a small imperative language.

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

This content is based on a tutorial presented at
[SSFT24](https://fm.csl.sri.com/SSFT24/) by David Thrane Christiansen,
co-developed with Leonardo de Moura.
