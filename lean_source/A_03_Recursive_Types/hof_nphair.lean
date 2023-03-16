def comp { α β γ : Type } (f : α → β ) (g : β → γ ) : α → γ :=
  fun (a : α), g (f a)

def inc (n : ℕ):= n + 1
def sqr (n : ℕ) := n * n

def inc_then_sqr := comp inc sqr

#reduce inc_then_sqr 5

/-
Need a function that takes a function and returns 1 less than its length
-/

-- How come I can call .length on this? Everywhere else it has been applying functions to values.
#eval [1,2,3].length
#eval list.length [1,2,3]
#eval nat.pred 5

#eval (comp list.length nat.pred) [1,2,3]

-- Function composition in prop. 'Comp' if function composition in type.
example (α β γ : Prop) : (α → β ) → (β → γ ) → (α → γ ) :=
 begin
 assume ab bg,
 assume a,
 exact bg (ab a),
 end 


 def inc_list_nat : list nat → list nat
 | list.nil := list.nil
 | (list.cons h t) := (nat.succ h)::(inc_list_nat t)

 #eval inc_list_nat [1,2,3]


 def any_list_nat : (nat → nat) → list nat → list nat
 | f list.nil := list.nil
 | f (h::t) := f h::any_list_nat f t


#eval any_list_nat nat.pred [1,2,3]


 def any_list_string: (string → nat) → list string → list nat
 | f list.nil := list.nil
 | f (h::t) := f h::any_list_string f t

 #eval any_list_string string.length ["I", "LOVE", "MATH"]


 def map_string_bool: (string → bool) → list string → list bool
 | f list.nil := list.nil
 | f (h::t) := f h::map_string_bool f t

-- want to return a lis to even and odd lengths
-- #eval map_string_bool (_) ["I", "LOVE", "MATH"]
-- need a function to be applied.

def is_even (n: nat) : bool := n % 2 = 0
#eval is_even 4

#eval map_string_bool (comp string.length is_even) ["I", "LOVE", "MATH"]



 def map {α β : Type} : (α → β) → list α → list β 
 | f list.nil := list.nil
 | f (h::t) := f h::map f t

#eval map (comp string.length is_even) ["I", "LOVE", "MATH"]
#eval map nat.succ [1, 2, 3]


def fold_nat:  (nat → nat → nat) → list nat → nat
| _ list.nil := 0
| op (h::t) := (op h) (fold_nat op t)


#eval fold_nat nat.add [1, 2, 3]

-- uh-oh, look at this.
#eval fold_nat nat.mul [1, 2, 3]
-- == 0. Our base case is not good for multiplication. We might want to pass this
-- default (call it the identity element) in.


def fold_nat2:  (nat → nat → nat) → nat → list nat → nat
| _ id list.nil := id
| op id (h::t) := (op h) (fold_nat2 op id t)


#eval fold_nat2 nat.mul 1 [1, 2, 3]


-- def fold_nat3:  (nat → nat → nat) → nat → list nat → nat
-- | op id list.nil := id
-- | op id (h::t::list.nil) := h
-- | op id (h::t) := (op h) (fold_nat3 op id t)
-- 
-- 
-- #eval fold_nat3 nat.add 5 [1,2,3]


-- lets path a proof that the second argumen is the identity of the operator.
def fold_nat4 
    (op: nat → nat → nat)
    (id: nat)
    (pf: ∀ (n: nat), op n id = n): list nat → nat
| list.nil := id
| (h::t) := op h (fold_nat4 t)

-- 0 is the identity element so we are good.
#eval fold_nat4 nat.add 0
begin
assume n,
simp [nat.add],
end
[1,2,3]

-- 1 is not the id element for addition.
#eval fold_nat4 nat.add 1
begin
assume n,
simp [nat.add],
sorry,
end
[1,2,3]

-- for fold, I need a set of objects, and operation, and an identity element.
-- these are examples of an algebraic structures we can generalize. This is called
-- a monoid. A monoid, is a set of objects, an operation, and identity element, a proof
-- of the id element, and a proof the operation is associative.
