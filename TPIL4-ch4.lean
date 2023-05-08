


section problem_1
  -- try it 
  variable (α : Type) (p q : α → Prop)

  example : (∀ x, p x ∧ q x) ↔ (∀ x, p x) ∧ (∀ x, q x) := 
    Iff.intro
    (
      fun h : ∀ x, p x ∧ q x =>
      ⟨ fun y => (h y).left, fun y => (h y).right ⟩ 
    )
    (
      fun h :  (∀ x, p x) ∧ (∀ x, q x) =>
        fun y => ⟨ h.left y, h.right y ⟩ 
    )


  example : (∀ x, p x → q x) → (∀ x, p x) → (∀ x, q x) := 
    fun h1 : ∀ x, p x → q x =>
      fun h2 : ∀ x, p x =>
        fun y => (h1 y) (h2 y)


  example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := 
    fun h : (∀ x, p x) ∨ (∀ x, q x) =>
      Or.elim h
      ( fun hp :∀ x, p x => fun y : α => Or.inl (hp y))
      ( fun hq :∀ x, q x => fun y : α => Or.inr (hq y)) 

end problem_1



section problem_2

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  example : α → ((∀ x : α, r) ↔ r) :=
    fun a : α =>
      Iff.intro
      ( fun h : (∀ x : α, r) => h a )
      ( fun hr : r => fun x: α => hr )


  open Classical

  example : (∀ x, p x ∨ r) ↔ (∀ x, p x) ∨ r := 
    Iff.intro
    ( fun h : ∀ x, p x ∨ r => 
        byCases
          (fun hr : r => Or.inr hr )
          (fun hnr : ¬r =>
            Or.inl ( 
              fun x : α => Or.elim (h x)
                ( fun hp : p x => hp )
                ( fun hr : r   => absurd hr hnr )
            ) 
          )
    )
    (
      fun h : (∀ x, p x) ∨ r =>
          Or.elim h
          ( fun ha : (∀ x, p x) => fun y => Or.inl (ha y) )
          ( fun hr : r          => fun _ => Or.inr hr )
    )


  example : (∀ x, r → p x) ↔ (r → ∀ x, p x) := 
    Iff.intro
    ( fun h : ∀ x, r → p x => 
        fun hr : r => fun x => (h x) hr )
    (
      fun h : r → ∀ x, p x => 
        fun x => 
          fun hr : r => (h hr) x
    )


end problem_2


section problem_3

  -- try it 
  variable (men : Type) (barber : men)
  variable (shaves : men → men → Prop)

  -- open Classical

  -- example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
  --   have h' : shaves barber barber ↔ ¬ shaves barber barber := h barber
  --   byCases
  --   ( fun hs : shaves barber barber => ( h'.mp hs) hs )
  --   ( fun hns : ¬ shaves barber barber => hns ( h'.mpr  hns) )


  example (h : ∀ x : men, shaves barber x ↔ ¬ shaves x x) : False := 
    have h' : shaves barber barber ↔ ¬ shaves barber barber := h barber
    have key ( p : Prop ) : ¬( p ↔ ¬ p) :=
      fun h :  p ↔ ¬ p => 
        have hnp : ¬p := fun hp : p => (h.mp hp) hp
        hnp (h.mpr hnp)
    key (shaves barber barber) h'



end problem_3



section problem_4
-- try it 
def even (n : Nat) : Prop := 
  ∃ k, n = 2*k

def divides (k : Nat) (n : Nat) :=
  ∃ k' : Nat, n = k*k'


def prime (n : Nat) : Prop := 
  ∀ a b : Nat, divides n (a*b) → (divides n a ) ∨ (divides n b)

def irred (n : Nat) : Prop := 
  ∀ n' : Nat, divides n' n -> ( n' = 1 ) ∨ ( n' = n )


def infinitely_many_primes : Prop := 
  ∀ N : Nat, ∃ n : Nat, n ≥ N ∧ prime n 

def Fermat_prime (n : Nat) : Prop := 
   prime (2^2^n + 1)

def infinitely_many_Fermat_primes : Prop := 
  ∀ N : Nat, ∃ n : Nat, n ≥ N ∧ Fermat_prime n 


-- def goldbach_conjecture : Prop := 
--   ∀ n : Nat, even n → n > 2 → ∃ p q : Nat, prime p ∧ prime q ∧ n = p + q

def Goldbach's_weak_conjecture : Prop := sorry

def Fermat's_last_theorem : Prop := 
  ¬ ∃ a b c n : Nat, a > 0 ∧ b > 0 ∧ c > 0 ∧ n > 2 ∧ a^n + b^n = c^n 



end problem_4



section problem_5
  -- try it 
  open Classical

  variable (α : Type) (p q : α → Prop)
  variable (r : Prop)

  theorem dne {p : Prop} (h : ¬¬p) : p :=
    Or.elim (em p)
      (fun hp : p => hp)
      (fun hnp : ¬p => absurd hnp h)

  example (a : α) : r → (∃ _ : α, r) := 
      fun hr : r => ⟨ a, hr ⟩  

  example : (∃ x, p x ∧ r) ↔ (∃ x, p x) ∧ r := 
    Iff.intro
    ( fun h : ∃ x, p x ∧ r => 
        match h with
        | ⟨ ( y : α  ), ( hy :  p y ∧  r) ⟩  => ⟨ ⟨ y, hy.left ⟩, hy.right ⟩
    )
    ( fun h : (∃ x, p x) ∧ r =>
        match h with
        | ⟨ ⟨  (y : α), (hy : p y) ⟩, ( hr : r ) ⟩  =>  ⟨ y, hy, hr ⟩ 
    )


  example : (∃ x, p x ∨ q x) ↔ (∃ x, p x) ∨ (∃ x, q x) :=
    Iff.intro
    ( fun h : ∃ x, p x ∨ q x => 
        let ⟨ (y : α ), ( hy :  p y ∨ q y ) ⟩ := h
        Or.elim hy
          (fun hp : p y => Or.inl ⟨ y, hp ⟩)
          (fun hq : q y => Or.inr ⟨ y, hq ⟩)
    )
    ( fun h : (∃ x, p x) ∨ (∃ x, q x) => 
      Or.elim h
      ( fun hp : ∃ x, p x => 
          let ⟨ y, hpy ⟩ := hp 
          ⟨ y, Or.inl hpy ⟩ 
      )
      ( fun hq : ∃ x, q x => 
          let ⟨ y, hqy ⟩ := hq
          ⟨ y, Or.inr hqy ⟩
      )
    )


  example : (∀ x, p x) ↔ ¬ (∃ x, ¬ p x) := 
    Iff.intro 
    ( fun hp : (∀ x, p x) => fun h2 : (∃ x, ¬ p x) =>
        Exists.elim h2
        ( fun y => fun hnp => absurd (hp y) hnp )
    )
    ( fun h1 : ¬ (∃ x, ¬ p x) =>   
        fun a : α =>
          byContradiction  
          (
            fun hnp : ¬ p a =>
              show False from h1 ⟨ a, hnp ⟩
          )
    )

  example : (∃ x, p x) ↔ ¬ (∀ x, ¬ p x) := 
    Iff.intro
    (
      fun h1 : ∃ x, p x => 
      Exists.elim h1
      ( fun y (hy : p y) =>
        fun hp : (∀ x, ¬ p x) =>
          absurd hy (hp y)
      )
    )
    (
      fun ha :  ¬ (∀ x, ¬ p x) => 
        byContradiction 
        (
          fun hne : ¬ (∃ x, p x) =>
            have key : ∀ x, ¬ p x :=
              fun y : α => 
                fun hp : p y => hne ⟨ y, hp ⟩
            absurd key ha
        )    
    )


  example : (¬ ∃ x, p x) ↔ (∀ x, ¬ p x) := 
    Iff.intro
    (
      fun h : ¬ ∃ x, p x =>
        fun y : α =>
          fun hp : p y =>
            show False from h ⟨ y, hp ⟩
    )
    ( 
      fun h : ∀ x, ¬ p x =>
        byContradiction
        (
          fun he : ¬ ¬ ∃ x, p x =>
            have he' : ∃ x, p x := dne he
            let ⟨ y, hp ⟩ := he'
            absurd hp (h y)
        )
    )


    
  -- example : (¬ ∀ x, p x) ↔ (∃ x, ¬ p x) := sorry

  example : (∀ x, p x → r) ↔ (∃ x, p x) → r := 
    Iff.intro
    (
      fun h : (∀ x, p x → r) => 
        fun he : (∃ x, p x) => 
          Exists.elim he
          ( fun ( y :α ) ( hp : p y ) => 
            show r from h y hp 
          )
    )
    (
      fun h : (∃ x, p x) → r =>
        fun y : α => 
          fun hp : p y =>
            show r from h ⟨ y, hp ⟩ 
    )



  example (a : α) : (∃ x, p x → r) ↔ (∀ x, p x) → r := 
    Iff.intro
    (
      fun h : ∃ x, p x → r =>
        fun ( ha : ∀ x, p x ) =>
          Exists.elim h
          ( fun y (hr : p y → r ) => 
            show r from hr (ha y) )
    )
    (
      fun h : (∀ x, p x) → r =>
        byCases
        ( fun ha1 : ∀ x, p x => 
          have ha : p a → r :=
            fun hpa : p a => h ha1
          ⟨ a, ha ⟩ 
        )
        (
          fun ha2 : ¬∀ x, p x =>
            have he : ∃ x, ¬ p x := 
              byContradiction
              ( 
                fun hne : ¬ ( ∃ x, ¬ p x ) => show False from 
                  have ha : ∀ x, p x := 
                    ( fun y : α =>
                      byContradiction
                      (
                        fun hnp : ¬ p y =>
                          show False from hne ⟨ y, hnp ⟩ 
                      )
                    )
                  absurd ha ha2
              )
            Exists.elim he
            ( fun y ( hnp : ¬p y) =>
                ⟨ y, fun hp : p y => absurd hp hnp ⟩   
            )
        )
    )  

  -- example r ↔ ¬ ¬ r :=
  --   rfl


  example (a : α) : (∃ x, r → p x) ↔ (r → ∃ x, p x) := 
    Iff.intro
    (
      fun h : (∃ x, r → p x) => 
        let ⟨ x, hx ⟩ := h
        fun hr : r => 
          ⟨ x, hx hr ⟩ 
    )
    ( 
      fun h : (r → ∃ x, p x) =>
        byCases
        (
          fun hr : r => 
            let ⟨ x, hx ⟩ := h hr
            show ∃ x, r → p x from
              ⟨ x, fun _ : r => hx ⟩ 
        )
        (
          fun hnr : ¬ r =>
            show ∃ x, r → p x from
              ⟨ a, fun hr : r => absurd hr hnr ⟩ 
        )
    )





end problem_5
