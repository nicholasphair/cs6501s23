-- Stubbed out basic types
inductive concept | mk
inductive event | mk
inductive action | mk
-- inductive bool_expr | mk
inductive app_state | mk
inductive bool_var | mk

inductive aexp : Type
  | ANum (n : nat)
  | APlus (a1 a2 : aexp)
  | AMinus (a1 a2 : aexp)
  | AMult (a1 a2 : aexp).

inductive bool_expr : Type 
  | BTrue
  | BFalse
  | BEq (a1 a2 : aexp)
  | BNeq (a1 a2 : aexp)
  | BLe (a1 a2 : aexp)
  | BGt (a1 a2 : aexp)
  | BNot (b : bool_expr)
  | BAnd (b1 b2 : bool_expr)
 
def bool_env_type : Type := bool_var → bool
 
variables
 (bool_env : bool_var → bool)
 (bool_expr_eval : bool_expr → bool_env_type → bool)
 
inductive app 
| atomic (c : concept) 
| seq (a1 a2 : app)
| if_then_else (c : bool_expr) (t : app) (f : app)
| while (c : bool_expr) (b : app)
| weave (a : app) (b: app)
open app
  
 
def app_eval : app → app_state → unit
| a st := unit.star
 
-- account for runtime event/action wiring and setup for that separately
 
variables 
 (thermometer survey resources auth: app)
 (condition : bool_expr)
 
/-
Here's a model of our app. Dooes it capture it (but for the outer loop)?
-/
-- instructions in imperative programs have well defined impacts on state. so too must our concepts.
def md : app := 
 seq 
  auth
  (while (condition)
   (seq 
    (thermometer)
    (if_then_else (condition)
      (seq survey resources) -- survey and 
      (resources)
    ) 
   )
  )

notation a `;;` b := seq a b
notation `if` condition `then` a `else` b := if_then_else condition a b
notation `while` condition `do` a := while condition a
notation a `⇝` b := weave a b

def md2 : app :=
  auth;; 
  while condition do
    thermometer;;
    if condition then
      (survey;;resources)
    else
      resources



variables (not_authd : bool_expr)

def md3 : app :=
  while not_authd do auth;;
  while condition do
    thermometer;;
    if condition then
      (
        weave auth survey;;
        weave auth resources
      )
    else
      weave auth resources


def md4 : app :=
  auth ⇝ 
    thermometer;;
    if condition then
      (
        survey;;
        resources
      )
    else
      resources



variables 
 (condition1 : bool_expr)

def md5 : app :=
  auth ⇝ 
    while condition1 do 
        thermometer;;
        if condition1 then (
            survey;;
            resources )
        else
          resources