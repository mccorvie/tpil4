
/- 
As an exercise, you should think about what the introduction 
and elimination rules for these types do. As a further exercise, 
we suggest defining boolean operations and, or, not on the Bool 
type, and verifying common identities. 
-/

namespace Hidden

def and (a b : Bool) : Bool :=
  match a with
  | true  => b
  | false => false

def or (a b : Bool) : Bool := 
  match a with 
  | false => b
  | true  => true

def not (a : Bool ) : Bool := 
  match a with 
  | false => true
  | true  => false


example { a : Bool } : ( or a (not a) ) = true := 
  match a with
  | true => rfl
  | false => rfl


example : not (and a b) = or (not a) (not b) := by
  cases a <;> cases b <;> rfl


example : and a (and b c) = and (and a b) c := 
  match a with
  | false => rfl
  | true  => 
    match b with
    | false => rfl
    | true  => 
      match c with
      | false => rfl
      | true  => rfl


example : and a false = false := by 
  cases a <;> rfl


end Hidden

#eval false ∧ true

#check false
#check False

/-
As exercises, we encourage you to develop a notion of composition 
for partial functions from α to β and β to γ, and show that it 
behaves as expected. 
-/

-- try it 
namespace Hidden2

inductive Option (α : Type u) where
  | none : Option α
  | some : α → Option α


def composition {α β γ :Type} 
  (f : α → Option β) 
  (g : β → Option γ ) : α → Option γ :=
    fun (a : α) =>
      match f a with
      | Option.none   => Option.none
      | Option.some b => g b

end Hidden2


/-
We also encourage you to show that Bool and 
Nat are inhabited, that the product of two inhabited types is 
inhabited, and that the type of functions to an inhabited type 
is inhabited.
-/

namespace Hidden3

inductive Inhabited (α : Type u) where
  | mk : α → Inhabited α


def inat  : Inhabited Nat := Inhabited.mk 100
def ibool : Inhabited Bool := Inhabited.mk true

#check inat
#check ibool

example ( iα : Inhabited α ) ( iβ : Inhabited β ) : 
  Inhabited (α × β) := by
  let ⟨a⟩ := iα 
  let ⟨b⟩ := iβ  
  exact ⟨ a, b ⟩

example (a : α ) (b : β ) : α × β :=
  ( a, b )


example ( α β : Type u ) (iβ : Inhabited β ) : 
  Inhabited ( α → β ) := by
  let ⟨b⟩ := iβ 
  exact Inhabited.mk ( fun _ => b )

end Hidden3



-- try it 
namespace Hidden4

inductive List (α : Type u) where
  | nil  : List α
  | cons : α → List α → List α

namespace List
  def append (as bs : List α) : List α :=
    match as with
    | nil       => bs
    | cons a as => cons a (append as bs)

  theorem nil_append (as : List α) : append nil as = as :=
    rfl

    -- List.recOn
    -- ( motive := fun as => append nil as = as )
    -- as
    -- ( show append nil nil = nil from rfl )
    -- ( fun ( a : α ) (as : List α) (ih : append nil as = as) =>
    --   show append nil (cons a as) = cons a as from rfl
    -- )

#check List.recOn

theorem cons_append (a : α) (as bs : List α) : 
        append (cons a as) bs = cons a (append as bs) :=
  rfl


theorem append_nil (as : List α) : append as nil = as :=
    List.recOn
    ( motive := fun as => append as nil = as )
    as
    ( show append nil nil = nil from rfl )
    ( fun ( a : α ) (as : List α) (ih : append as nil = as) =>
        show append (cons a as) nil = cons a as from
        calc 
          append (cons a as) nil = cons a (append as nil) := rfl
          _                      = cons a as              := by rw [ih] )


#print List.recOn


theorem append_assoc (as bs cs : List α)
        : append (append as bs) cs = append as (append bs cs) :=
    List.recOn
    ( motive := fun as => append (append as bs) cs = append as (append bs cs) )
    as
    ( show append (append nil bs) cs = append nil (append bs cs) from rfl )
    ( fun ( a : α ) (as : List α) (ih : append (append as bs) cs = append as (append bs cs) ) =>
        show append (append (cons a as) bs) cs = append (cons a as) (append bs cs) from
        calc append (append (cons a as) bs) cs 
--          _ = append (cons a (append as bs)) cs := by rfl
          _ = cons a (append (append as bs) cs) := by rfl
          _ = cons a (append as (append bs cs)) := by rw[ih]
          _ = append (cons a as) (append bs cs) := by rfl ) 
   

/-
Try also defining the function length, that returns the length of a
list, and prove that it behaves as expected
-/

def length : List α → Nat := 
  fun (as : List α)  =>
    match as with
    | nil       => 0
    | cons _ as => 1 + length as


theorem len_add  (as bs : List α) : length (append as bs) = length as + length bs := 
  List.recOn
  ( motive := fun as => length (append as bs) = length as + length bs )
  as
  ( show length (append nil bs) = length nil + length bs from
      calc length (append nil bs) 
        _ = length bs     := by rfl
        _ = 0 + length bs := by simp
        _ = length nil + length bs := by rfl
  )
  (
    fun ( a : α ) (as : List α) (ih : length (append as bs) = length as + length bs ) =>
      show length (append (cons a as) bs) = length (cons a as) + length bs from
        calc length (append (cons a as) bs)
          _ = 1 + length (append as bs)      := by rfl
          _ = 1 + (length as + length bs)    := by rw[ih]
          _ = 1 + length as + length bs      := by simp[Nat.add_assoc] 
          _ = length (cons a as) + length bs := by rfl
  )


-- Define some operations on lists, like a length function or the reverse function. 
-- Prove some properties, such as the following:

-- theorem len_add2 : length (s ++ t) = length s + length t := sorry

def reverse : List α → List α := 
  fun as => match as with
  | List.nil        => nil
  | List.cons a as2 => append (reverse as2) (List.cons a nil) 


def ll1 := List.cons 3 (List.cons 2 (List.cons 1 nil))

#check ll1
#print ll1

def ll1_r := reverse ll1

theorem len_reverse (t : List α ) : length (reverse t) = length t := 
  List.recOn
  ( motive := fun as => length (reverse as) = length as )
  t
  ( show length (reverse nil) = length nil from rfl )
  (
    fun ( a : α ) (as : List α) (ih : length (reverse as) = length as ) =>
      show length ( reverse (cons a as) ) = length (cons a as) from
        calc length ( reverse (cons a as) ) 
          _   = length (append (reverse as) (List.cons a nil)) := by rfl
          _   = length (reverse as) + length (List.cons a nil) := by rw[len_add] 
          _   = length as + 1   := by rw[ih]; rfl
          _   = 1 + length as   := by simp[Nat.add_comm]
          _   = length (cons a as)  := by rfl
  )

theorem rev_append (as bs : List α ) : reverse ( append as bs ) = append (reverse bs) (reverse as) :=
  List.recOn
  ( motive := fun ll => reverse (append ll bs) = append (reverse bs) (reverse ll))
  as
  ( show reverse (append nil bs) = append (reverse bs) nil by rw[append_nil]; rfl )
  (
    fun ( a : α ) (as : List α) (ih : reverse (append as bs) = append (reverse bs) (reverse as) ) =>
      calc reverse (append (cons a as) bs)
        _   = reverse (cons a (append as bs)) := by rfl
        _   = append (reverse (append as bs)) (cons a nil) := by rfl
        _   = append (append (reverse bs) (reverse as)) (cons a nil) := by rw[ih]
        _   = append (reverse bs) (append (reverse as) (cons a nil)) := by rw[append_assoc]
        _   = append (reverse bs) (reverse (cons a as)) := by rfl
  )


-- theorem rev_list1 (a : α ) : reverse (cons a nil) = cons a nil :=
--   rfl

theorem rev_rev ( t : List α ) : reverse (reverse t) = t := 
  List.rec
  ( motive := fun as => reverse (reverse as) = as )
  ( show reverse (reverse nil) = nil from rfl )
  (
    fun ( a : α ) (as : List α) (ih : reverse (reverse as) = as ) =>
      show reverse ( reverse (cons a as) ) = cons a as from
        calc reverse ( reverse (cons a as) ) 
          _   = reverse ( append (reverse as) (cons a nil)) := by rfl
          _   = append (reverse (cons a nil)) (reverse (reverse as)) := by rw[rev_append]
          _   = cons a as := by rw[ih]; rfl
  )
  t


end List

end Hidden4


namespace Hidden5

/-
Its not hard to prove that Eq is a symmetric and transitive.  In
the following example, we prove symm and leave as exercises the 
theorems of trans and congr
-/

-- #check (@Eq.rec : {α : Sort u} → 
--   {a : α} → 
--   {motive : (x : α) → a = x → Sort v} → 
--   motive a rfl → 
--   {b : α} → 
--   (h : a = b) → motive b h)

#check Eq.rec

#check Eq
#check Eq.refl
#check rfl


-- try it 
-- namespace Hidden
-- inductive Eq {α : Sort u} (a : α) : α → Prop where
--   | refl : Eq a a
-- end Hidden

theorem subst0 {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  Eq.rec (motive := fun x _ => p x) h₂ h₁


theorem subst {α : Type u} {a b : α} {p : α → Prop} (h₁ : Eq a b) (h₂ : p a) : p b :=
  match h₁ with
  | rfl => h₂ 


theorem symm {α : Type u} {a b : α} (h : Eq a b) : Eq b a := 
  Eq.rec (motive := fun x _ => Eq x a) rfl h

-- theorem symm' {α : Type u} {a b : α} (h : Eq a b) : Eq b a := by
--   let p : α → Prop := fun x => Eq x a
--   have : p a := rfl
--   exact Eq.subst h this

theorem symm' {α : Type u} {a b : α} (h : Eq a b) : Eq b a := 
  match h with
  | rfl => rfl


theorem trans {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := 
  match h₁ with
  | rfl => h₂

theorem trans' {α : Type u} {a b c : α} (h₁ : Eq a b) (h₂ : Eq b c) : Eq a c := 
  let p : α -> Prop := fun x => Eq a x
  have : p b := h₁
  subst h₂ this


theorem congr {α β : Type u} {a b : α} (f : α → β) (h : Eq a b) : Eq (f a) (f b) := 
  match h with
  | rfl => rfl


end Hidden5


namespace Hidden6

/-
Define an inductive data type consisting of terms built up from the 
following constructors:
  const n : a constant denoting the natural number n
  var n : a variable numbered n
  plus s t : denoting the sum of s and t
  times s t : denoting the product of s and t

Recursively define a function that evaluates any such term with
respect to an assignment of values to the variables
-/  

-- inductive Bool where
--   | false : Bool
--   | true  : Bool


inductive Expr where 
| const : Nat → Expr
| var   : Nat → Expr
| plus  : Expr → Expr → Expr
| times : Expr → Expr → Expr


def ee := Expr.times (Expr.plus (Expr.const 2) (Expr.var 1)) (Expr.const 5)

def EvalExpr (ex : Expr) ( v : Nat → Nat ) : Nat :=
  match ex with
  | Expr.const n => n
  | Expr.var n   => v n
  | Expr.plus ex1 ex2 => (EvalExpr ex1 v) + (EvalExpr ex2 v)
  | Expr.times ex1 ex2 => (EvalExpr ex1 v) * (EvalExpr ex2 v)


#eval EvalExpr ee id


end Hidden6



namespace Hidden7

/-
Similarly define the type of propositional formulas, as well as functions
on the type of such formulas: an evaluation function, functions that measure
the complexity of a formula, and a function that substitutes another
formula for a given variable.
-/

inductive PForm where 
| const : Bool → PForm
| var   : Nat  → PForm
| and   : PForm → PForm → PForm
| or    : PForm → PForm → PForm
| not   : PForm -> PForm


def EvalPForm (pf : PForm) ( v : Nat → Bool ) : Bool :=
  match pf with
  | PForm.const b   => b
  | PForm.var n     => v n
  | PForm.and pf1 pf2 => (EvalPForm pf1 v) ∧ (EvalPForm pf2 v)
  | PForm.or pf1 pf2  => (EvalPForm pf1 v) ∨ (EvalPForm pf2 v)
  | PForm.not pf'     => ¬(EvalPForm pf' v)


def pf := PForm.or (PForm.not (PForm.const true)) (PForm.and (PForm.not (PForm.var 1)) (PForm.var 2))

def vv1 : Nat → Bool := fun _ => false

#eval EvalPForm pf vv1

def Complexity (pf : PForm) : Nat :=
  match pf with
  | PForm.const _ => 1
  | PForm.var _   => 1
  | PForm.and pf1 pf2 => 1 + max (Complexity pf1) (Complexity pf2)
  | PForm.or pf1 pf2  => 1 + max (Complexity pf1) (Complexity pf2)
  | PForm.not pf'     => 1 + Complexity pf'

#eval Complexity pf

#eval 1 = 0

def FormSubst (pf : PForm) (n : Nat) (pf' : PForm) : PForm :=
  match pf with
  | PForm.var m   => cond ( m == n ) pf' (PForm.var m) 
  | PForm.and pf1 pf2 => PForm.and (FormSubst pf1 n pf') (FormSubst pf2 n pf')
  | PForm.or pf1 pf2  => PForm.or (FormSubst pf1 n pf') (FormSubst pf2 n pf')
  | PForm.not pf0     => PForm.not (FormSubst pf0 n pf') 
  | PForm.const b     => PForm.const b


  -- | PForm.const b => PForm.const b
  -- | PForm.and pf1 pf2 => PForm.and pf1 pf2 
  -- | PForm.or pf1 pf2  => PForm.or pf1 pf2
  -- | PForm.not pf'     => PForm.not pf'
  
def pf1 := PForm.or (PForm.var 1) (PForm.var 2)
def pf2 := PForm.and (PForm.const true) (PForm.var 3)

def vv' ( n : Nat ) : Bool := 
  match n with
  | 1 => true
  | 2 => false
  | 3 => true
  | _ => true
  

#print PForm


#eval EvalPForm (pf1) (vv')

#eval EvalPForm (pf2) (vv')

#eval EvalPForm (FormSubst pf1 1 pf2) (vv')

end Hidden7

