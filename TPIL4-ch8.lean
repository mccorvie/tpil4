

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
  | _, zero   => zero
  | a, succ b => add (mul a b) a

#eval mul 5 7


def exp : Nat → Nat → Nat
  | _, zero   => 1
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
-/

namespace hidden3

variable (C : Nat → Type u)
--#check (@Nat.below C : Nat → Type u)
--#reduce @Nat.below C (3 : Nat)
--#check (@Nat.brecOn C : (n : Nat) → ((n : Nat) → @Nat.below C n → C n) → C n)

open Nat

-- f(n) = f(n-1) + f(n-2) + ... + f(0)
-- f(0) = 1

-- prove by induction f(n) = 2^n

def cov_f0 (n : Nat) : Nat :=
  let rec loop : Nat → Nat 
    | 0   => 1
    | m+1 => cov_f0 m + loop m 
  loop n

#eval cov_f0 10

-- think: below f n = [ f 0 , f 1 , f 2 , ..., f n ]

def below ( f : Nat → α ) : Nat → List α 
  | 0 => []
  | m + 1 => (f m) :: below f m

variable (ff : Nat → Nat)

#reduce below ff 5

-- f n = f (n-1) + f (n-2) + ... + f 0
--#eval List.foldr (.+.) 0 [1,2,3,4]

-- failed to prove termination
-- def cov_f : (n : Nat) → Nat :=
--   fun n => (below cov_f n).foldr (.+.) 1


def cov_f1 : (n : Nat ) → Nat :=
  fun n => 
    let rec cov_below : Nat → List Nat
      | 0 => []
      | m+1 => (cov_f1 m) :: cov_below m
    (cov_below n).foldr (.+.) 1

#eval cov_f1 4



mutual
  def below' : Nat → List Nat
    | 0 => []
    | m + 1 => (cov_f' m) :: below' m
      
  def cov_f' : (n : Nat) → Nat := 
    fun n => (below' n).foldr (.+.) 1
end

#eval cov_f' 16


/-
Similarly, see if you can figure out how to define 
WellFounded.fix on your own.
-/


-- The first, Acc, is an inductively defined predicate. According to its 
-- definition, Acc r x is equivalent to ∀ y, r y x → Acc r y. If you think 
-- of r y x as denoting a kind of order relation y ≺ x, then Acc r x says 
-- that x is accessible from below, in the sense that all its predecessors 
-- are accessible. In particular, if x has no predecessors, it is accessible. 
-- Given any type α, we should be able to assign a value to each accessible 
-- element of α, recursively, by assigning values to all its predecessors 
-- first.

-- The statement that r is well founded, denoted WellFounded r, is exactly 
-- the statement that every element of the type is accessible. By the above 
-- considerations, if r is a well-founded relation on a type α, we should 
-- have a principle of well-founded recursion on α, with respect to the 
-- relation r. And, indeed, we do: the standard library defines 
-- WellFounded.fix, which serves exactly that purpose.


variable (α : Type ) (r : α → α → Prop) (C : α → Sort v) 
#check @Acc.rec



-- noncomputable def f {α : Sort u}
--       (r : α → α → Prop)
--       (h : WellFounded r)
--       (C : α → Sort v)
--       (F : (x : α) → ((y : α) → r y x → C y) → C x)
--       : (x : α) → C x := WellFounded.fix h F

-- WellFounded.fix {r : α → α → Prop} (h : WellFounded r)
--  ( F : (x : α ) → ((y : α ) → r y x → C y) → C x )


noncomputable def WellFounded.fix 
  ( hwf : WellFounded r ) 
  ( F : (x : α) → ((y : α) → r y x → C y) → C x ) : 
  ( x : α ) → C x := by 
    intro x
    match hwf with
    | ⟨ hwf2 ⟩ =>      
      induction hwf2 x with
      | intro x hx h_ih  => exact F x h_ih


end hidden3








/-
Following the examples in Section Dependent Pattern 
Matching, define a function that will append two
vectors. This is tricky; you will have to define an
auxiliary function.
-/



namespace hidden4


inductive Vector (α : Type u) : Nat → Type u
  | nil  : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n+1)



def tailAux (v : Vector α m) : m = n + 1 → Vector α n :=
  Vector.casesOn 
    (motive := fun x _ => x = n + 1 → Vector α n) 
    v
    (fun h : 0 = n + 1 => Nat.noConfusion h)
    (fun (a : α) (m : Nat) (as : Vector α m) =>
     fun (h : m + 1 = n + 1) =>
       Nat.noConfusion h (fun h1 : m = n => h1 ▸ as))

def tail (v : Vector α (n+1)) : Vector α n :=
  tailAux v rfl

#check Vector.casesOn 


-- Vector.casesOn.{u_1, u} {α : Type u} 
--   {motive : (a : Nat) → Vector α a → Sort u_1} 
--   {a✝ : Nat} 
--   (t : Vector α a✝)
--   (nil : motive 0 Vector.nil) 
--   (cons : (a : α) → {n : Nat} → (a_1 : Vector α n) → 
--     motive (n + 1) (Vector.cons a a_1)) :
--   motive a✝ t


def vappendAux' (v : Vector α l) (ys : Vector α m) :
  (h : l + m = n) → Vector α n :=
  Vector.casesOn 
    (motive := fun x _ => x + m = n → Vector α n)
    v
    ( fun h : 0 + m = n =>  
        have : m = n := by simp at h; assumption
        this ▸ ys 
    )
    ( fun (x : α) (l : Nat) (xs : Vector α l) => 
      fun h : l + 1 + m = n => 
      let n' := l + m
      have hn' : n' = l + m := rfl
      have hh  : l + m + 1 = n := by
        rw [← h]
        simp [Nat.add_comm,Nat.add_assoc]
      
      hh ▸ Vector.cons x (vappendAux' xs ys hn')
    )

def vappend' (xs : Vector α m) (ys : Vector α n) : 
  (Vector α (m+n)) :=
  vappendAux' xs ys rfl

-- #check @Vector.casesOn
open Vector 
 

def vappendAux {α : Type u} : {l m : Nat} → 
    (Vector α l) → (Vector α m) → ((h : l + m = n) → Vector α n)
    | 0,   m, nil, ys => 
      fun ( h : 0+m = n ) => by
        simp at h
        exact h ▸ ys
    | l+1, m, cons x xs, ys => 
      fun (h : l+1+m = n) => by
        let n' := l + m
        have hn' : n' = l + m := rfl
        have h'  : l + m + 1 = n := by 
          rw [← h,Nat.add_assoc,Nat.add_comm m 1,Nat.add_assoc]
        exact  h' ▸ cons x (vappendAux xs ys hn')


def vappend (xs : Vector α m) (ys : Vector α n) : 
  Vector α (m+n) :=
  vappendAux xs ys rfl


def vv := Vector.cons 1 (Vector.cons 2 (Vector.cons 3 Vector.nil))


#print vv

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
  | const n     => n
  | var n       => v n
  | plus e₁ e₂  => eval v e₁ + eval v e₂
  | times e₁ e₂ => (eval v e₁) * (eval v e₂)

def sampleVal : Nat → Nat
  | 0 => 5
  | 1 => 6
  | _ => 0


-- Try it out. You should get 47 here.
#eval eval sampleVal sampleExpr

/-
Implement "constant fusion," a procedure that 
simplifies subterms like 5 + 7 to 12. 
Using the auxiliary function simpConst, define a 
function "fuse": to simplify a plus or a times, 
first simplify the arguments recursively, and then 
apply simpConst to try to simplify the result.
-/


def simpConst : Expr → Expr
  | plus (const n₁) (const n₂)  => const (n₁ + n₂)
  | times (const n₁) (const n₂) => const (n₁ * n₂)
  | e                           => e

def fuse : Expr → Expr 
  | plus  e₁ e₂ => simpConst (plus (fuse e₁) (fuse e₂))
  | times e₁ e₂ => simpConst (times (fuse e₁) (fuse e₂)) 
  | e           => e 



theorem simpConst_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (simpConst e) = eval v e := by
        sorry


theorem fuse_eq (v : Nat → Nat)
        : ∀ e : Expr, eval v (fuse e) = eval v e :=
  sorry


/-
The last two theorems show that the definitions 
preserve the value.
-/


end hidden5


/-
Bonus problem:
The map function is even more tedious to define 
by hand than the tail function. We encourage you 
to try it, using recOn, casesOn and noConfusion.
-/



