

/-
Open a namespace Hidden to avoid naming conflicts, 
and use the equation compiler to define addition, 
multiplication, and exponentiation on the natural 
numbers. Then use the equation compiler to derive 
some  of their basic properties.
-/

namespace hidden1

open Nat 

#print Eq.refl
#print rfl
#print rfl.proof_1

def add : Nat → Nat → Nat 
  | a, zero   => a
  | a, succ b => succ ( add a b ) 


#eval add 5 7


def mul : Nat → Nat → Nat 
  | a, zero   => zero
  | a, succ b => add (mul a b) a

#eval mul 5 7


def exp : Nat → Nat → Nat
  | a, zero   => 1
  | a, succ b => mul (exp a b) a


#eval exp 12 2
#eval exp 3 3


theorem add_assoc (a b : Nat) : ∀ (c : Nat), add (add a b) c = add a (add b c)
  | zero   => rfl
  | succ m => by simp [add, add_assoc]

theorem add_zero : ∀ n, add n 0 = n
  | _ => rfl

theorem zero_add : ∀ n, add 0 n = n 
  | zero   => rfl
  | succ n => by simp [add, zero_add]

theorem exp_zero : ∀ n, exp n 0 = 1
  | _ => rfl

theorem add_succ : ∀ (a b : Nat),
 add a (succ b) = succ (add a b) 
  | _, _ => rfl


theorem succ_add : ∀ ( a b : Nat ), 
  add (succ a) b = succ (add a b)
  | _, zero => rfl
  | _, succ m => by simp [add, succ_add]

-- theorem add_comm (a : Nat): ∀ (b : Nat), a+b = b+a
--   | zero   => by simp [zero_add, add_zero]
--   | succ m => by simp[succ_add, add_succ, add_comm] 

end hidden1


/-
Similarly, use the equation compiler to define some 
basic operations on lists (like the reverse function)
and prove theorems about lists by induction (such
as the fact that reverse (reverse xs) = xs for any 
list xs).
-/


namespace hidden2

open List 

def rev : (as : List α) → List α 
  | nil     => nil
  | a :: as => ( rev as ) ++ (a :: nil)

theorem append_assoc : ∀ (as bs cs : List α ),
  (as ++ bs) ++ cs = as ++ (bs ++ cs)
  | nil,  _, _ => rfl 
  | a :: as, _, _ => by simp[*, append_assoc]

theorem rev_append : ∀ (as bs : List α ), 
  rev (as ++ bs) = (rev bs) ++ (rev as)
  | nil, _      => by simp[*, rev]
  | a :: as, bs => by simp[*, rev, rev_append, append_assoc]

theorem rev_rev : ∀ ( ll : List α ), 
    rev (rev ll) = ll
  | nil     => by simp[*, rev]
  | a :: as => by simp[*,rev,rev_append,rev_rev]


end hidden2


/-
Define your own function to carry out 
course-of-value recursion on the natural numbers. 
Similarly, see if you can figure out how to define 
WellFounded.fix on your own.
-/



namespace hidden3



end hidden3



/-
Following the examples in Section Dependent Pattern 
Matching, define a function that will append two
vectors. This is tricky; you will have to define an
auxiliary function.
-/



namespace hidden4



end hidden4



/-
Consider the following type of arithmetic expressions. 
The idea is that var n is a variable, vₙ, and const n 
is the constant whose value is n.
-/

namespace hidden5

inductive Expr where
  | const : Nat → Expr
  | var : Nat → Expr
  | plus : Expr → Expr → Expr
  | times : Expr → Expr → Expr
  deriving Repr

open Expr

def sampleExpr : Expr :=
  plus (times (var 0) (const 7)) (times (const 2) (var 1))

/-
Here sampleExpr represents (v₀ * 7) + (2 * v₁).
-/


/-
Write a function that evaluates such an expression, 
evaluating each var n to v n.
-/

def eval (v : Nat → Nat) : Expr → Nat
  | const n     => sorry
  | var n       => v n
  | plus e₁ e₂  => sorry
  | times e₁ e₂ => sorry

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0


-- Try it out. You should get 47 here.
-- #eval eval sampleVal sampleExpr

/-
Implement "constant fusion," a procedure that 
simplifies subterms like 5 + 7 to 12. 
Using the auxiliary function simpConst, define a 
function "fuse": to simplify a plus or a times, 
first simplify the arguments recursively, and then 
apply vsimpConst to try to simplify the result.
-/


def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr := sorry

theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e :=
  sorry

theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry


/-
The last two theorems show that the definitions 
preserve the value.
-/

end hidden5

