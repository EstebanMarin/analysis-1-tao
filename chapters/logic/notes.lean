import Mathlib.Tactic


namespace Notes



variable (A B C : Prop)

section
#check A ∧ ¬ B → C

variable (h₁: A ∧ ¬B)

#check h₁

#check And.left h₁
#check And.right h₁

#check And.intro 
  (And.left h₁) 
  (And.left h₁)

example : A ∧ ¬ B → ¬B ∧ A := 
λ h : A ∧ ¬ B ↦ 
And.intro (And.right h) (And.left h)


-- better annotated
example (A B: Prop) : A ∧ ¬B → ¬B ∧ A :=
λ h₃: A ∧ ¬B ↦ 
show ¬B ∧ A from And.intro
  (show ¬B from And.right h₃)
  (show A from And.left h₃)

end
-- building natural deduction proofs

-- implication

section
  variable (C D: Prop)
  example : C → D :=
  λ h₁: C ↦ show D from sorry

  section
    variable (h1 : A → B) (h2 : A)

    example : B := h1 h2
  end
end

-- Conjunction

section
 variable (h₁: A) (h₂: B)
 example : A ∧ B := And.intro h₁ h₂
end 

section
  variable (h: A ∧ B)
  example : A := And.left h
  example : B := And.right h
end

-- Disjunction

section
  variable (h: A) (h₂: B)
  example : A ∨ B := Or.inl h
  example : A ∨ B := Or.inr h₂
end

section

  variable (h₁ : A ∨ B) (ha : A → C) (hb : B → C)
  example : C := 
    Or.elim h₁
      (λ h₁ : A ↦ show C from ha h₁)
      (λ h₁ : B ↦ show C from hb h₁)

end


-- Negation
section
-- impossible to prove
example : ¬ A :=
 λ h₁ : A ↦ show False from sorry

-- example
variable (h₁: A)(h₂ : ¬ A)
  example : False := h₂ h₁

end

section
variable (h: False) 
example : A := False.elim h
example : True := trivial
end
-- Bi - Implication
section
example: A ↔ B := 
 Iff.intro
  (λ h₁ : A ↦ show B from sorry)
  (λ h₂ : B ↦ show A from sorry)

section
variable (h₁: A ↔ B)(h₂: A)(h₃ : B)
example : B := Iff.mp h₁ h₂
example : A := Iff.mpr h₁ h₃
end 
end

-- proof by contradiction

section
  open Classical

  example : A :=
  byContradiction
    (fun h : ¬ A ↦
      show False from sorry)
end

-- example 
section
example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
λ h1 ↦ Or.elim (And.right h1)
  (λ h2 ↦ Or.inl (And.intro (And.left h1) h2))
  (λ h2 ↦ Or.inr (And.intro (And.left h1) h2))
end

-- TACTICS! 
section
-- term mode
example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) :=
fun h1 : A ∧ (B ∨ C) ↦
Or.elim (And.right h1)
  (fun h2 : B ↦
    show (A ∧ B) ∨ (A ∧ C) from Or.inl (And.intro (And.left h1) h2))
  (fun h2 : C ↦
    show (A ∧ B) ∨ (A ∧ C)
      from Or.inr (And.intro (And.left h1) h2))

example (A B C : Prop) : A ∧ (B ∨ C) → (A ∧ B) ∨ (A ∧ C) := by
  intro (h₁: A ∧ (B ∨ C))
  cases h₁ with 
      | intro h1 h2 => cases h2 with 
      | inl h2 =>
      apply Or.inl
      apply And.intro
      exact h1
      exact h2
      | inr h2 => 
      apply Or.inr
      apply And.intro
      exact h1
      exact h2

end

-- forward reasoning 
section Forward
variable (h₁ : A → B)(h₂ : B → C)

-- term mode
example : A → C := 
  λ ha : A ↦ 
  have hb : B := h₁ ha
  show C from h₂ hb



-- tactics entering with by 
example : A → C := by
   intro (ha: A)
   have hb: B := h₁ ha  
   show C 
   exact h₂ hb
end Forward
     
section theorems.Definition
def triple_and (A B C: Prop) : Prop := A ∧ (B ∨ C)
variable (D E F G : Prop)
#check triple_and (B ∧ C) (F ∧ G) (¬ F ∧ G)

theorem and_commute {A B: Prop}: A ∧ B → B ∧ A :=
  λ h ↦ And.intro (And.right h) (And.left h)

-- excercises 

section exercises 

example : A ∧ (A → B) → B := by
intro (h₁: A ∧ (A → B))
have ha: A := And.left h₁
have func:  A → B := And.right h₁
apply func ha


example : A → ¬ (¬ A ∧ B) := by
intro (ha: A)(hc: ¬ A ∧ B)
have notha: ¬A := And.left hc
apply notha ha

example : ¬ (A ∧ B) → (A → ¬ B) := by
intro (h₁: ¬ ( A ∧ B))(ha : A)(hb : B)
apply h₁ (And.intro ha hb)


example (h₁ : A ∨ B) (h₂ : A → C) (h₃ : B → D) : C ∨ D :=
sorry

example (h : ¬ A ∧ ¬ B) : ¬ (A ∨ B) :=



sorry

example : ¬ (A ↔ ¬ A) :=
sorry

end exercises


end theorems.Definition



end Notes
