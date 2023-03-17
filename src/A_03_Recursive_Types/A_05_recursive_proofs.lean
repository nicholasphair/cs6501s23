
def add : nat → nat → nat
| a  zero     := a
| a  (succ b) := succ (add a b)


example : ∀ (n : ℕ), nat.add n 0 = n :=
begin
assume n,
simp [nat.add],
end



example : ∀ n, nat.add nat.zero n = n :=
begin
assume n,
simp [nat.add],
-- oops, that didn't help; we're stuck!
end


example : ∀ n, nat.add nat.zero n = n :=
begin
assume n,
cases n with n',
-- first case: zero's also on the right
simp [nat.add],
-- second case, argument is succ of some n'
-- how to show 0 + (succ n') = (succ n')
-- but again we're stuck
simp [nat.add],
-- basically back where we started; stuck.
end


theorem zero_left_id_zero : nat.zero + nat.zero = nat.zero := 
begin
simp [nat.add],
end



theorem zero_left_id_one : 0 + 1 = 1 := 
begin
/-
Key idea: use *second* add axiom to rewrite 
add 0 (succ 0) to succ (0 + 0). Please be very
sure you understand this point. The new goal
to prove is thus as follows: 
-/ 
show 1 + (0 + 0) = 1,  
/-
And now, the second key idea: We can use the
proof we already have to rewrite 0 + 0 as 0,
and at that point Lean sees that the proof can
be finished by applying rfl. 
-/
rw zero_left_id_zero,
/-
We have thus constructed a proof of 0 + 1 = 1
from a proof of 0 + 0 = 0. Can we do it again
to get a proof for *a = 2*? Yes, we can.
-/
end  

theorem zero_left_id_two : 0 + 2 = 2 :=
begin
-- apply second rule of addition
show 1 + (1 + 0) = 2,
-- apply proof already constructed for *a = 1*
rewrite zero_left_id_one,
end 


def left_id_step (a' : ℕ) : 
  nat.add 0 a' = a' → 
  nat.add 0 (a'.succ) = (a'.succ) :=
  begin
  assume induction_hypothesis,
  simp [nat.add],   -- by second rule for add
  assumption,       -- by induction hypothesis
  end



def zero_left_ident_any_a : ∀ (a : ℕ), (nat.add 0 a = a) 
| 0 := zero_left_id_zero
| (nat.succ a') := (left_id_step a' (zero_left_ident_any_a a'))

#check zero_left_ident_any_a


-- eyeball check of the recursive structure of these proofs!
#reduce zero_left_ident_any_a 0     -- the proof term is unpretty (just eyeball it)
#reduce zero_left_ident_any_a 1     -- the proof for 1 buids on the proof for 0
#reduce zero_left_ident_any_a 2     -- the proof for 2 buids on the proof for 1
                                -- and we see we can build such a proof for any n
                                -- therefore 0 is a left identity for addition




/- 
Here's the definition of list.append.
It asserts that [] is a left identity axiomatically. 

def append : list α → list α → list α
| []       l := l
| (h :: s) t := h :: (append s t)
-/

-- proving right identity is trivial just as for addition
example (α : Type) : ∀ (l : list α), list.nil ++ l = l :=
begin
assume l,
simp [list.append],
end

/-TEXT:
We run into the same problem as we did before if we take a
naive approach to trying to prove that nil is also a left
identity for ++. And the solution is once again to define
a recursive function by case analysis on l that constructs
a proof of *nil ++ l = l* for any list l. If l = list.nil,
the proof of nil ++ nil is given by the first rule of list
append, otherwise l = (h::t), and we need to prove that
nil ++ h::t = h::t. By the second axiom of list append,
we can rewrite nil ++ h::t as h::(nil ++ t), where we can
obtain (and then us) a proof that nil ++ t = t by recursion,
terminating when t =nil. 

Fortunately, Lean's library already contains a proof that
nil is a right identity, and it's annotated as *[simp]*,
which means that the *simp* tactic will try to use it to
prove our goal. In other words, we can use [simp] to prove
the harder case precisely because someone else has already
done the work for us; and they did it recursively just as
we did to show that 0 is a right identity for addition. 

def nil_left_ident_app (α : Type) : ∀ (l : list α), l ++ list.nil = l :=
begin
assume l,
cases l with h t,
-- base case
simp [list.append],   -- uses first rule
-- recursive case
simp [list.append],   -- why does this work?
end 

-- Here's another formal demonstration of the same point
variables (α : Type) (a : α) (l : list α) 
example: list.nil ++ l = l := by simp    -- first rule
example : l ++ list.nil  = l := by simp  -- by [simp] lemma in Lean library



inductive le (n : nat): nat → Prop 
-- n is an implicit firt argument to each constructor
| refl : le /-n-/ n     
| step : ∀ m, le /-n-/ m → le /-n-/ m.succ

-- you can see it in the types of the constructors
#check @le.refl
#check @le.step


example : le 0 0 :=
begin
apply le.refl,
end 

example : le 3 3 :=
begin
apply le.refl,
end 

example : le 0 1 :=
begin
apply le.step,
apply le.refl,
end 

example : le 0 3 :=
begin
apply le.step,
apply le.step,
apply le.step,
apply le.refl,
end 

-- here's the same example using Lean's version of "le"
-- it's called nat.less_than_or_equal
example : 0 ≤ 3 :=
begin
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.step,
-- apply nat.less_than_or_equal.step,
apply nat.less_than_or_equal.refl,
end 

-- repeat tactical goes too far; use iterate instead
example : 1 ≤ 4 :=
begin
-- repeat {apply nat.less_than_or_equal.step},
iterate 3 {apply nat.less_than_or_equal.step},
apply nat.less_than_or_equal.refl,
end 
