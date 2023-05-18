
inductive CTree where
  | black : Nat → CTree
  | red   : Nat → CTree
  | branch : CTree → CTree → CTree
  
open CTree

def sum : CTree → Nat
  | black n => n
  | red n   => n
  | branch t₁ t₂ => sum t₁ + sum t₂

def simpColor : CTree → CTree
  | branch (red n₁) (red n₂)    => red (n₁ + n₂)
  | branch (black n₁) (black n₂) => black (n₁ + n₂)
  | e                           => e

theorem simpColor_eq1
        : ∀ e : CTree, sum (simpColor e) = sum e := by
    intro e
    match e with
    | branch (red n₁) (red n₂)     => rfl
    | branch (black n₁) (black n₂) => rfl
    | e                            => rfl -- failure in overmatching case? 

theorem simpColor_eq2
        : ∀ e : CTree, sum (simpColor e) = sum e := by
    intro e
    match e with
    | red n => rfl
    | black n => rfl
    | branch t₁ t₂ => 
        match t₁, t₂ with
        | red n₁,     red n₂       => rfl
        | black n₁,   black n₂     => rfl
        | red n₁,     black n₂     => rfl
        | black n₁,   red n₂       => rfl
        | branch _ _, _            => rfl
        | _,          branch _ _   => simp [simpColor] -- why doesn't this work with rfl?

variable (t1 t2 t3 : CTree)
example : simpColor (branch t1 (branch t2 t3)) = branch t1 (branch t2 t3) := by simp [simpColor]


theorem simpColor_eq
        : ∀ e : CTree, sum (simpColor e) = sum e := by
    intro e
    rw [simpColor]
    split <;> rfl

example : simpColor (branch (branch t1 t2) t3) = branch (branch t1 t2) t3 := by rfl
example : simpColor (branch (red m) (red n)) = red (m+n):= by rfl
example : simpColor (branch (red m) (black n)) = branch (red m) (black n) := by rfl



def tt := branch (red 1) (branch t1 t2)

#print tt
#reduce simpColor tt
 


    -- intro e
    -- simp [simpConst]
    
    -- rw [simpConst]
    -- rfl
    -- cases simpConst
    -- case plus (const n₁) (const n₂) =>
    -- match e with
    -- | plus (const n₁) (const n₂)  => rfl
    --   -- calc eval v (simpConst (plus (const n₁) (const n₂))) 
    --   --   -- _ = eval v (const (n₁ + n₂)) := rfl
    --   --   -- _ = n₁ + n₂ := rfl
    --   --   -- _ = eval v (const n₁) + eval v (const n₂) := rfl
    --   --   _ = eval v (plus (const n₁) (const n₂)) := rfl
    -- | times (const n₁) (const n₂)  => rfl 
    --   -- calc eval v (simpConst (times (const n₁) (const n₂))) 
    --   --   _ = eval v (const (n₁ * n₂)) := rfl
    --   --   _ = n₁ * n₂ := rfl
    --   --   _ = (eval v (const n₁))  * (eval v (const n₂)) := rfl
    --   --   _ = eval v (times (const n₁) (const n₂)) := rfl
    -- | _  => rfl 
    --   -- have : simpConst e = e := by rw [simpConst]
    --   -- rw [this]

