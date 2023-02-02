
/- TEXT:

**********************
A Better Specification
**********************

In this chapter we present an improved specification
of the syntax and semantics of propositional logic. As
usual, we first present the syntax specification then the
semantics.

Syntax
------
TEXT. -/

namespace cs6501

-- QUOTE:
-- variables, still indexed by natural numbers
inductive prop_var : Type
| mk (n : ℕ)

-- examples
def v₀ := prop_var.mk 0
def v₁ := prop_var.mk 1
def v₂ := prop_var.mk 2
-- QUOTE. 

/- TEXT:
We will now refactor our definition of 
prop_expr to factor out mostly repeated code 
and to make explicit (1) a class of *literal*
expressions, and (2) binary operators as first
class citizens and a class of corresponding
binary operator expressions. Be sure to compare
and contrast our definitions here with the ones in
the last chapter.

We'll start by defining a *binary operator* type
whose values are abstract syntax terms for binary
operators/connectives in propositional logic.
TEXT. -/

-- QUOTE:
-- Syntactic terms for binary operators
inductive binop
| opAnd
| opOr
| opImp
| opIff
| opXor
| opNand
| opNor

inductive unop
| opNot


open binop
open unop

-- A much improved language syntax spec
inductive prop_expr : Type
| pLit (b : bool)                         -- literal expressions
| pVar (v: prop_var)                      -- variable expressions
| pUnOp (op: unop) (e : prop_expr)        -- unary operator expression
| pBinOp (op : binop) (e1 e2 : prop_expr) -- binary operator expressions

open prop_expr


-- An example of an "and" expression
def an_and_expr := 
  pBinOp 
    opAnd                   -- binary operator
    (pVar (prop_var.mk 0))  -- variable expression
    (pVar (prop_var.mk 1))  -- variable expression

-- An example of a "not" expression
def a_not_expr := 
  pUnOp 
    opNot                   -- unary operator
    (pVar (prop_var.mk 3))  -- variable expression
-- QUOTE.

/- TEXT:
We have to update the previous notations definitions,
which now need to *desugar* to use the new expression
constructors. We also define some shorthands for the
two literal expressions in our language.
TEXT. -/


-- QUOTE:
reserve notation `↓`:37 x:37
def True := pLit tt
def False := pLit ff
notation (name := pVar) `[` v `]` :=  pVar v
notation (name := pAnd) e1 ∧ e2 :=  pBinOp opAnd e1 e2
notation (name := pOr) e1 ∨ e2 :=  pBinOp opOr e1 e2
notation (name := pNot) ¬e := pUnOp opNot e
notation (name := pImp) e1 => e2 := pBinOp opImp e1 e2
notation (name := pIff) e1 ↔ e2 := pBinOp opIff e1 e2
notation (name := pXor) e1 ⊕ e2 := pBinOp opXor e1 e2
<<<<<<< HEAD
notation (name := pNand) e1 ↑ e2 := pBinOp opNand e1 e2
notation (name := pNor) e1 ↓ e2 := pBinOp opNor e1 e2 
=======

-- Precedence highest to lowest NOT, NAND, NOR, AND, OR, ->, ==
-- `↓`:37 x:37
reserve notation `↓`:37 x:37
notation (name := pNor) e1 `↓` e2 := pBinOp opAnd e1 e2

#print notation ¬ 
#print notation ∧ 
#print notation ↑
#print notation ↓ 
>>>>>>> 0756ffca914ffbcda4296a3fa5735bde7a92b037

-- QUOTE.


/- TEXT:
Here are examples of expressions using our concrete syntax
TEXT. -/

-- QUOTE:
-- variable expressions from variables
def X := [v₀]
def Y := [v₁]
def Z := [v₂]

-- operator expressions
def e1 := X ∧ Y
def e2 := X ∨ Y
def e3 := ¬Z
def e4 := e1 => e2
def e5 := e1 ↔ e1
def e6 := X ⊕ ¬X
def e7 := X  ↑ ¬X
def e8 := X  ↓ ¬X
-- QUOTE.

/- TEXT:
Semantics
---------

A benefit of having made binary operators 
explicit as a set of syntactic terms is that
we can simultaneously simplify and generalize 
our semantics. 
TEXT. -/

-- QUOTE:
-- Helper functions
def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

def biff : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := ff
| ff ff := tt
-- QUOTE.

<<<<<<< HEAD
def bnand : bool → bool → bool
| tt tt := ff
| tt ff := tt
| ff tt := tt
| ff ff := tt


def bnor : bool → bool → bool
| tt tt := ff
| tt ff := ff
| ff tt := ff
| ff ff := tt

/-
We now define an *interpretation* for operator symbols!
Each binop (a syntactic object) has as its meaning some
corresponding binary Boolean operator.

-/
=======
/- TEXT:
We now define an *interpretation* for operator symbols!
Each binop (a syntactic object) has as its meaning some
corresponding binary Boolean operator.
TEXT. -/

-- QUOTE:
>>>>>>> 0756ffca914ffbcda4296a3fa5735bde7a92b037
def op_sem : binop → (bool → bool → bool)
| opAnd := band 
| opOr  := bor
| opImp := bimp
| opIff := biff
| opXor := bxor
| opNand := bnand
| opNor := bnor


def uop_sem : unop → (bool → bool)
| unNot := bnot 


-- A quick demo
#reduce ((op_sem opAnd) tt ff)
#reduce (op_sem opOr tt ff) -- recall left associativity
-- QUOTE.

/- TEXT:
Now here's a much improved semantic specification.
In place of rules for pTrue and pFalse we just have
one rule for pLit (literal expressions). Second, in
place of one rule for each binary operator we have
one rule for *any* binary operator. 
TEXT. -/

-- QUOTE:
def pEval : prop_expr → (prop_var → bool) → bool
<<<<<<< HEAD
| (pLit b) i := b 
| ([v]) i := i v                -- our [] notation on the left
| (pUnOp op e) i := uop_sem op (pEval e i)
| (pBinOp op e1 e2) i := (op_sem op) (pEval e1 i)  (pEval e2 i) 
=======
| (pLit b)          i := b 
| ([v])             i := i v                  -- our [] notation on the left
| (¬e)              i := bnot (pEval e i)     -- our ¬ notation; Lean's bnot
| (pBinOp op e1 e2) i := (pEval e1 i) && (pEval e2 i) -- BUG!
>>>>>>> 0756ffca914ffbcda4296a3fa5735bde7a92b037
-- QUOTE.

-- Nick's prop_vars
def npv₀ := prop_var.mk 7
def npv₁ := prop_var.mk 8
def npv₂ := prop_var.mk 9

def npE₀ := [npv₀]
def npE₁ := [npv₁]
def npE₂ := [npv₂]

def my_not_true := ¬True
def my_nand_expr := (True ↑ True) ∨ False
def my_cool_expr := my_not_true ↑ my_nand_expr
def my_cool_expr_2 := npE₀ ↑ npE₁ ↓ npE₂
def my_cool_expr_3 := npE₀ ∧ npE₁ ∧ npE₂


-- The interprets of Nick's prop_vars
def nicks_state_1 : prop_var → bool
| _ := ff

-- Why can i not say npv₁ 
def nicks_state_2: prop_var → bool
| (prop_var.mk 7) := ff
| (prop_var.mk 8) := tt
| (prop_var.mk 9) := ff
| _ := ff


def result_a1 := pEval my_not_true nicks_state_1  --  ff
def result_a2 := pEval my_nand_expr nicks_state_1  --  ff
def result_a3 := pEval my_cool_expr_2 nicks_state_1  -- tt
def result_a4 := pEval my_cool_expr_3 nicks_state_1  -- ff
#reduce result_a1
#reduce result_a2
#reduce result_a3
#reduce result_a4

def result_b1 := pEval my_not_true nicks_state_2  --  ff
def result_b2 := pEval my_nand_expr nicks_state_2  --  ff
def result_b3 := pEval my_cool_expr_2 nicks_state_2 -- tt - operator precedence of nor > nand
def result_b4 := pEval my_cool_expr_3 nicks_state_2  -- ff
#reduce result_b1
#reduce result_b2
#reduce result_b3
#reduce result_b4

/- TEXT:
<<<<<<< HEAD
Here are a few exercises:
  - identify and fix the bug in the last rule of pEval
  - replace pNot with pUnOp ("unary operator"), as with pBinOp
  - update the first rule in pEval to use the new concrete notation --- not sure this is possible. We have just defined TRUE and FALSE, not made any syntax changes.
  - add end-to-end support for nand (↑) and nor (↓) binary operators
  - write some propositional logic expressions using concrete syntax
  - define some interpretations and evaluate your expressions under each
=======

Exploration
-----------

You've heard about Lean and seen in it action, but there's no substitute for
getting into it yourself. The goal of this exploration is for you to "connect 
all the dots" in what we've developed so far, and for you to start to develop 
"muscle memory" for some basic Lean programming. 

  - Identify and fix the bug in the last rule of pEval
  - Replace pNot with pUnOp ("unary operator"), as with pBinOp
  - Add end-to-end support for logical *nand* (↑) and *nor* (↓) expression-building operators
  - Define some examples of propositional logic expressions using concrete syntax
  - Define several interpretations and evaluate each of your expressions under each one

To avoid future git conflicts, make a copy of src/04_prop_logic_syn_sem.lean, and 
make changes to that file rather than to the original. Bring your completed work 
to our next class. Be prepared to share and/or turn in your work at the beginning
of next class.

>>>>>>> 0756ffca914ffbcda4296a3fa5735bde7a92b037
TEXT. -/



theorem and_commutes :
  ∀ (e1 e2: prop_expr)   -- for all e1 e2
    (i: prop_var -> bool),  -- for any interpretation i
    (pEval (e1 ∧ e2) i) = (pEval (e2 ∧ e1) i) -- show the order doesnt matter
    := -- and now we need a proof. and if we can prove our proposition, i dont need tests, i it holds for any inpput
    begin
      assume e1 e2 i,
      unfold pEval, -- exapnding my expressions
      unfold op_sem,
      cases (pEval e1 i), 
      cases (pEval e2 i),
      apply rfl,
      apply rfl,
      cases (pEval e2 i),
      apply rfl,
      apply rfl
    end

-- left of turnstyle are assumption
-- cnd-shift-return lists goals, what i have left to do
-- tactics let me incrementaly work up to a goal
-- unfold is a tctic
-- reflexitivity (rfl), theorem in our library


-- after setting up our language and the semantics, now we are validating
-- that our semantics are correct.

def x : ℕ := 3 -- just as we check that 3 is a nat, we check above that is a valid proof.

end cs6501

