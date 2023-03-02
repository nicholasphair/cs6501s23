/- TEXT: 
*****************
Polymorphic Lists
*****************
TEXT. -/

-- QUOTE:
#check list
-- QUOTE.


-- this is MORE than just syntactic pattern matching
-- this is unification - a combination of of pattern matching and naming of subpatterns.
def pred : nat → nat
| nat.zero := nat.zero
| (nat.succ x) := x


def pred' : nat → nat :=
begin
assume n,
cases n,
exact 0,
exact n,
-- exact nat.succ(nat.succ n) -- There is nothing special about this implementation. Just as my pred function can be wrong, this can be wrong to. Only once I impment the nat axioms can I know my implementation is correct.
-- it is a valid proof, it type checks - does this mean anything.
end

def sub2 : nat → nat
| nat.zero := nat.zero
| (nat.succ(nat.succ x)) := x
| (nat.succ x) := nat.zero


#eval pred' 6 -- these sanity checks are like unit tests.


def tail: ∀ {α : Type}, list α → list α 
| α list.nil := list.nil
| α (list.cons h t) := t  -- destructuring the list

def tail_nice: ∀ {α : Type}, list α → list α 
| α list.nil := list.nil
| α (h::t) := t  -- destructuring the list

-- looks just like our natural number pred :) 

#eval tail [1,2,3,4]



-- def head: ∀ {α : Type}, list α → list α 
-- | α list.nil := __   -- WHAT DO I PUT HERE? I Need 
-- | α (list.cons h t) := head t 


def head: ∀ {α : Type}, list α → option α 
| α list.nil := none
| α (list.cons h t) := some h

#eval head [1,2,3]
#eval @head nat []  -- turn of implicit arguments.


-- I want a proof that the list is nonempty
--   if you give me an α, l, and a proof that l is not empty
def head': ∀ {α : Type} (l : list α), (l ≠ list.nil) → α
| α l p := 
begin 
cases l,
contradiction,
exact l_hd,
end

-- we called a function with a proof about its arguments
-- we would not be able to call this function if the list was empty!
#eval head' [1,2,3] 
begin
contradiction,
end