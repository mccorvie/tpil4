
section ch3a
  -- try it 
  variable (p q r : Prop)

  theorem ff (h : p ∧ q) : q ∧ p :=
    have hp : p := h.left
    have hq : q := h.right
    show q ∧ p from And.intro hq hp

    #check ff



  -- commutativity of ∧ and ∨
  theorem ff2 : p ∧ q ↔ q ∧ p := 
    Iff.intro
      ( fun h : p ∧ q =>
        show q ∧ p from ⟨  h.right, h.left ⟩ 
      )
      ( fun h : q ∧ p =>
        show p ∧ q from ⟨ h.right, h.left ⟩ 
      )


  example : p ∨ q ↔ q ∨ p := 
    ⟨ 
      fun h : p ∨ q => Or.elim h (fun hp : p => Or.inr hp) (fun hq : q => Or.inl hq ),
      fun h : q ∨ p => Or.elim h (fun hq : q => Or.inr hq) (fun hp : p => Or.inl hp )
    ⟩ 



  -- associativity of ∧ and ∨
  example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := 
    Iff.intro
      ( fun h : (p ∧ q) ∧ r => 
        show  p ∧ (q ∧ r) from ⟨ h.left.left, ⟨ h.left.right, h.right ⟩ ⟩
      ) 
      ( fun h : p ∧ (q ∧ r ) => 
        show ( p ∧ q ) ∧ r from ⟨ ⟨ h.left, h.right.left ⟩, h.right.right ⟩
      ) 


  example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := 
  Iff.intro
  ( fun h : (p ∨ q) ∨ r =>
      Or.elim h
        ( fun h1 : p ∨ q =>
          Or.elim h1 
          ( fun hp : p => Or.inl hp )
          ( fun hq : q => Or.inr (Or.inl hq ))
        )
        ( fun hr : r => Or.inr (Or.inr hr ))
  )
  ( fun h : p ∨ (q ∨ r) => 
      Or.elim h
        ( fun hp : p => Or.inl (Or.inl hp))
        ( fun h1 : (q ∨ r) =>
          Or.elim h1
          ( fun hq : q => Or.inl (Or.inr hq) )
          ( fun hr : r => Or.inr hr )
        )
    )


  -- distributivity
  example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := 
    ⟨
      fun h1: p ∧ (q ∨ r) => 
        Or.elim h1.right
          (fun hq : q => Or.inl (And.intro h1.left hq))
          (fun hr : r => Or.inr (And.intro h1.left hr )),

      
      fun h2: (p ∧ q) ∨ (p ∧ r) => 
      Or.elim h2
      ( fun hpq : p ∧ q => ⟨ hpq.left, Or.inl hpq.right ⟩ )
      ( fun hpr : p ∧ r => ⟨ hpr.left, Or.inr hpr.right ⟩ )
    ⟩




  example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := 
    ⟨
      fun hd :  p ∨ (q ∧ r) =>  
        Or.elim hd
        ( fun hp : p => ⟨ Or.inl hp, Or.inl hp ⟩ )
        ( fun hqr : q ∧ r => ⟨ Or.inr hqr.left, Or.inr hqr.right ⟩ ),


      fun hc : (p ∨ q) ∧ (p ∨ r) =>
        Or.elim hc.left
        ( fun hp : p => Or.inl hp )
        ( fun hq : q => 
          Or.elim hc.right
          ( fun hp2 : p => Or.inl hp2 )
          ( fun hr : r => Or.inr ( And.intro hq hr ) )
        )
    ⟩



  -- other properties
  example : (p → (q → r)) ↔ (p ∧ q → r) := 
    ⟨
      fun hpqr1 : p → (q → r) => 
        fun hpq : p ∧ q => hpqr1 hpq.left hpq.right,
      fun hpqr2 : p ∧ q → r => 
        fun hp : p =>
          fun hq : q => hpqr2 ⟨ hp, hq ⟩ 
    ⟩ 



  example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := 
    ⟨
      fun hd : (p ∨ q) → r =>
        ⟨ fun hp : p => hd (Or.inl hp), fun hq : q => hd (Or.inr hq) ⟩,
      
      fun hc : (p → r) ∧ (q → r) =>
        fun hpq : p ∨ q =>
          Or.elim hpq
          ( fun hp : p => hc.left hp )
          ( fun hq : q => hc.right hq )
    ⟩

    


  example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := 
    ⟨
      fun h : ¬(p ∨ q) => 
      ⟨ fun hp : p => h (Or.inl hp), fun hq : q => h (Or.inr hq) ⟩,

      fun h : ¬p ∧ ¬q =>
      ( fun hpq : (p ∨ q) => 
        Or.elim hpq
        ( fun hp : p => h.left hp )
        ( fun hq : q => h.right hq )
      )
    ⟩ 


  example : ¬p ∨ ¬q → ¬(p ∧ q) := 
    fun hc : ¬p ∨ ¬q =>
      Or.elim hc 
      ( fun hnp : ¬p => 
        fun hd : p ∧ q => absurd hd.left hnp )
      ( fun hnq : ¬q => 
        fun hd : p ∧ q => absurd hd.right hnq )


  example : ¬(p ∧ ¬p) := 
    fun h : p ∧ ¬p => h.right h.left 


  example : p ∧ ¬q → ¬(p → q) := 
    fun h : p ∧ ¬q =>
      fun hn : p → q => h.right (hn h.left)

  example : ¬p → (p → q) := 
    fun hnp : ¬p =>
      fun hp : p => absurd hp hnp


  example : (¬p ∨ q) → (p → q) := 
    ( fun h : (¬p ∨ q) => 
      Or.elim h
      ( fun hnp : ¬p => 
        ( fun hp : p => absurd hp hnp )
      )
      ( 
        fun hq : q =>
        ( fun hp : p => show q from hq )
      )
    )




  example : p ∨ False ↔ p := 
    ⟨
      fun h : p ∨ False => 
        Or.elim h
        ( fun hp : p => hp )
        ( fun hf : False => False.elim hf ),

      fun h : p => Or.inl h
    ⟩ 



  example : p ∧ False ↔ False := 
    ⟨
      fun h : p ∧ False => h.right,
      fun h : False => False.elim h
    ⟩
    

example : ¬(p ↔ ¬p) := 
  fun h : p ↔ ¬p => 
    
    match h with
    | ⟨ h1, h2 ⟩  =>




  example : (p → q) → (¬q → ¬p) := 
    fun h : p → q =>
      ( fun hnq : ¬q => 
        ( fun hp : p  => hnq (h hp) ))


end ch3a



section ch3b

  open Classical

  variable (p q r : Prop)

  example : (p → q ∨ r) → ((p → q) ∨ (p → r)) := 
    fun h :  (p → q ∨ r) =>
    byCases
    ( fun hp : p => 
      Or.elim (h hp)
      ( fun hq : q => Or.inl (fun _ : p => hq ))
      ( fun hr : r => Or.inr (fun _ : p => hr ))
    )
    ( fun hnp : ¬p =>
      Or.inl ( fun hp2 : p => absurd hp2 hnp )
    )

  example : ¬(p ∧ q) → ¬p ∨ ¬q := 
    fun hpq : ¬(p ∧ q) => 
    byCases 
    ( fun hp : p => 
        have hnq : ¬q := fun hq : q => hpq ⟨ hp, hq ⟩ 
        Or.inr hnq 
    )
    ( fun hnp : ¬p => Or.inl hnp )  


  example : (p → q) → (¬p ∨ q) := 
    fun h : (p → q) =>
    Or.elim (em p)
    ( fun hp : p => Or.inr (h hp))
    ( fun hnp : ¬p => Or.inl hnp )


  example : (¬q → ¬p) → (p → q) := 
    fun h : ¬q → ¬p =>
      fun hp : p => 
        have hq : q :=  
          byContradiction
          ( fun hnq : ¬q => h hnq hp)
        hq


  example : p ∨ ¬p := (em p)

  example : (((p → q) → p) → p) := 
    fun h1 : ((p → q) → p) =>
      byCases
      ( fun hp : p => hp )
      ( fun hnp : ¬p => 
        have h2 : p → q := ( fun hp2 : p => absurd hp2 hnp )
        h1 h2
      )

  example : ¬(p → q) → p ∧ ¬q := 
    fun h : ¬(p → q) =>
    byCases 
    ( fun hp : p => 
      byCases
      ( fun hq : q => absurd (fun _ :p  => hq) h )
      ( fun hnq : ¬q => ⟨ hp, hnq ⟩ )
    )
    ( fun hnp : ¬p => 
      have hpq : p → q :=
        (fun hp : p => absurd hp hnp)
      absurd hpq h 
    )

end ch3b