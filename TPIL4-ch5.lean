

section problem_1a

-- Chapter 3
variable (p q r : Prop)

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := by
  apply Iff.intro
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left
  . intro h
    apply And.intro
    . exact h.right
    . exact h.left


example : p ∨ q ↔ q ∨ p := by
  apply Iff.intro
  . intro h
    cases h with
    | inl h1 => apply Or.inr; exact h1
    | inr h2 => apply Or.inl; exact h2
  . intro h
    cases h with
    | inl h1 => apply Or.inr; exact h1
    | inr h2 => apply Or.inl; exact h2

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := by
  apply Iff.intro
  . intro h
    cases h with 
    | intro hpq _ => 
      cases hpq with
      | intro _ _ => 
        constructor
        assumption
        constructor
        repeat assumption
  . intro h 
    cases h with 
    | intro _ hqr =>
      cases hqr with 
      | intro _ _ =>
        constructor
        constructor
        repeat assumption




example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := by
  apply Iff.intro
  . intro h
    match h with 
    | Or.inl hpq => 
      match hpq with
      | Or.inl hp => apply Or.inl; assumption
      | Or.inr hq => apply Or.inr; apply Or.inl; assumption
    | Or.inr hr   => apply Or.inr; apply Or.inr; assumption
  . intro h
    match h with 
    | Or.inl hp => apply Or.inl; apply Or.inl; assumption
    | Or.inr hqr => 
      match hqr with
      | Or.inl hq => apply Or.inl; apply Or.inr; assumption
      | Or.inr hr => apply Or.inr; assumption


-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨ hp, Or.inl hq ⟩ => apply Or.inl; constructor <;> assumption
    | ⟨ hp, Or.inr hr ⟩ => apply Or.inr; constructor <;> assumption
  . intro 
    | Or.inl ⟨ hp, hq ⟩ => constructor; assumption; exact Or.inl hq
    | Or.inr ⟨ hp, hr ⟩ => constructor; assumption; exact Or.inr hr

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := by
  apply Iff.intro
  . intro
    | Or.inl hp  => constructor <;> apply Or.inl <;> assumption
    | Or.inr ⟨ hq, hr ⟩  => 
      constructor
      . apply Or.inr; assumption
      . apply Or.inr; assumption
  . intro ⟨ h1, h2 ⟩ 
    cases h1 with
    | inl => apply Or.inl; assumption
    | inr hq =>
      cases h2 with
      | inl => apply Or.inl; assumption
      | inr hr => apply Or.inr; constructor <;> assumption
 

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := by
  apply Iff.intro
  . intros h1 h2
    match h2 with
    | ⟨ _, _ ⟩ =>  apply h1 <;> assumption
  . intros h1 hp hq
    apply h1
    constructor <;> assumption

example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := by
  apply Iff.intro
  . intro h
    constructor <;> intro <;> apply h
    . apply Or.inl; assumption
    . apply Or.inr; assumption
  . intros h1 h2
    cases h2 with
    | inl h => exact h1.left h
    | inr h => exact h1.right h




example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := by
  apply Iff.intro 
  . intro h
    constructor <;> intro <;> apply h
    . apply Or.inl
      assumption
    . apply Or.inr
      assumption
  . intro ⟨ hnp, hnq ⟩
    intro h
    cases h
    case inl h => contradiction
    case inr h => contradiction

    
example : ¬p ∨ ¬q → ¬(p ∧ q) := by
  intro 
  | Or.inl _ => intro ⟨ _, _ ⟩; contradiction
  | Or.inr _ => intro ⟨ _, _ ⟩; contradiction


example : ¬(p ∧ ¬p) := by
  intro 
  | ⟨ hp, hnp ⟩ => contradiction

example : p ∧ ¬q → ¬(p → q) := by
  intro
  | ⟨ hp, hnq ⟩ => 
      intro hpq
      have hq : q := hpq hp
      contradiction

example : ¬p → (p → q) := by
  intros hnp hp
  contradiction

example : (¬p ∨ q) → (p → q) := by
  intro
  | Or.inl _ => simp [*]
  | Or.inr _ => simp [*]

example : p ∨ False ↔ p := by
  simp

  -- constructor
  -- . intro 
  --   | Or.inl _ => assumption
  --   | Or.inr _ => contradiction
  -- . intro 
  --   apply Or.inl
  --   assumption

example : p ∧ False ↔ False := by
  simp

  -- apply Iff.intro
  -- . intro ⟨ _, _⟩ 
  --   contradiction
  -- . intro 
  --   contradiction

examle : (p → q) → (¬q → ¬p) := by
  intros hpq _ hp
  have : q := hpq hp
  contradiction  


end problem_1a



-- From chapter 3 using classical
section problem_1b

open Classical

variable (p q r : Prop)

/--
  by_cases hp : p
  apply byContradiction
  apply Or.elim( em p )

  in mathlib.tactics
  push_neg
  contrapose
--/

example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := by
  intro h
  by_cases hp : p
  . cases h hp with
    | inl hq => apply Or.inl; intro; assumption
    |inr hr => apply Or.inr; intro; assumption
  . apply Or.inl; intro; contradiction


example : ¬(p ∧ q) → ¬p ∨ ¬q := by
  intro
  by_cases hp : p
  . by_cases hq : q
    . have hc : p ∧ q := by constructor <;> assumption
      contradiction
    . exact Or.inr hq
  . exact Or.inl hp


example : ¬(p → q) → p ∧ ¬q := by 
  intro
  by_cases hp : p
  . by_cases hq : q
    . have : p → q := by intro; assumption
      contradiction
    . exact ⟨ hp, hq ⟩
  . have : p → q := by intro; contradiction
    contradiction


example : p ∨ ¬p := by
  by_cases hp : p 
  case inl => apply Or.inl; assumption
  case inr => apply Or.inr; assumption


example : (p → q) → (¬p ∨ q) := by
  intro h
  simp [*]



  -- by_cases hp : p
  -- case inl => exact Or.inr (h hp)
  -- case inr => exact Or.inl hp



example : (¬q → ¬p) → (p → q) := by
  intros h hp 
  apply byContradiction
  intro hnq
  have := h hnq
  contradiction

example : (((p → q) → p) → p) := by
  intro h
  by_cases hp : p
  . assumption
  . have : p → q := by intro; contradiction
    exact h this

end problem_1b

-- From Chapter 4

section problem_1c

variable (α : Type) (p q : α → Prop)

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor
    . intro x₀
      exact (h x₀).left
    . intro x₀
      exact (h x₀).right
  . intros h x₀
    cases h with
    | intro h1 h2 => exact ⟨ h1 x₀, h2 x₀ ⟩ 



example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := by
  constructor
  . intro h
    constructor <;> intro x₀
    . exact (h x₀).left
    . exact (h x₀).right
  . intro h x₀
    exact ⟨ h.left x₀, h.right x₀ ⟩ 


example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := sorry
example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := sorry

-- try it 
variable (α : Type) (p q : α → Prop)
variable (r : Prop)

example : α → ((∀ x : α, r) ↔ r) := sorry
example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := sorry
example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := sorry


end problem_1c




section problem_2

example (p q r : Prop) (hp : p)
        : (p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) := by
        repeat try apply And.intro; repeat ( first | apply Or.inl; assumption | apply Or.inr | assumption)







--         apply And.intro
--         apply Or.inl; assumption
--         apply And.intro
-- --        apply Or.inl; assumption
--         apply Or.inr
-- --        assumption
--         apply Or.inl; assumption
--         apply And.intro


--    repeat ( first | apply Or.inl; assumption | apply Or.inr | assumption) ; try constructor


        -- constructor
        -- repeat ( first | apply Or.inl; assumption | apply Or.inr | assumption)



--  repeat (first | repeat ( first | apply Or.inl; assumption | apply Or.inr | assumption) | constructor)

  
  
  


end problem_2


