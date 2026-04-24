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

-- Bi - Implication
section
example: A ↔ B := 
 Iff.intro
  (λ h₁ : A ↦ show B from sorry)
  (λ h₂ : B ↦ show A from sorry)
end



end


end Notes
