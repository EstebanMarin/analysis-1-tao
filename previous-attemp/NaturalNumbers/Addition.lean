/-
# Addition World

In this world, we'll prove fundamental properties of addition
on natural numbers using mathlib.
-/

-- https://github.com/ReallyLiri/lean-natural-number-game-solutions/tree/main/2_Addition_World 

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace NaturalNumbersGame

/-
## Level 1: Addition with zero

Prove that adding zero on the right gives the same number.
Hint: This is `Nat.add_zero` in mathlib.
-/

-- https://github.com/leanprover-community/NNG4/blob/main/Game/Levels/Addition/L01zero_add.lean
-- https://www.youtube.com/watch?v=136e2d8pWlc
theorem add_zero (n : ℕ) : n + 0 = n := by
  induction n with
  | zero => exact Nat.zero_add 0
  | succ d hd => rw [Nat.add_succ];  

/-
## Level 2: Zero on the left

Prove that adding zero on the left gives the same number.
Hint: This is `Nat.zero_add` in mathlib.
-/

theorem zero_add (n : ℕ) : 0 + n = n := by
  induction n with
  | zero => rw[Nat.add_zero]
  | succ d hd => rw [Nat.add_succ]; rw[hd];

/-
## Level 3: Successor on the right

Prove that `n + succ m = succ (n + m)`.
Hint: Use `Nat.add_succ`.
-/

theorem add_succ (n m : ℕ) : n + Nat.succ m = Nat.succ (n + m) := by
  induction n with
  | zero => rfl
  | succ a d => rfl



/-
## Level 4: Successor on the left

Prove that `succ n + m = succ (n + m)`.
Hint: Use `Nat.succ_add`.
-/

theorem succ_add (n m : ℕ) : Nat.succ n + m = Nat.succ (n + m) := by
  exact? -- exact Nat.succ_add n m

/-
## Level 5: Commutativity of addition

Prove that addition is commutative.
Hint: Use `Nat.add_comm`.
-/

theorem add_comm (n m : ℕ) : n + m = m + n := by
  exact?

/-
## Level 6: Associativity of addition

Prove that addition is associative.
Hint: Use `Nat.add_assoc`.
-/

theorem add_assoc (a b c : ℕ) : (a + b) + c = a + (b + c) := by
  rw [Nat.add_assoc]

/-
## Level 7: Using induction

Now let's prove something using induction.
We'll prove `zero_add` from scratch without using the library lemma.
-/

theorem zero_add_induction (n : ℕ) : 0 + n = n := by
  induction n with
  | zero =>
    -- Base case: 0 + 0 = 0
    exact?
  | succ n ih =>
    -- Inductive step: assume 0 + n = n (hypothesis `ih`),
    -- prove 0 + succ n = succ n
    exact?

/-
## Level 8: More complex proof

Prove this using commutativity and previous lemmas.
-/

theorem add_left_cancel (a b c : ℕ) (h : a + b = a + c) : b = c := by
  exact?

/-
## Challenge Exercises
-/

theorem add_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
  exact?

theorem succ_eq_add_one (n : ℕ) : Nat.succ n = n + 1 := by
  exact?


theorem succ_addd (a b : ℕ) : Nat.succ a + b = Nat.succ (a + b) := by
  induction b with
  | zero => rfl
  | succ b h₁ => rw [Nat.add_succ, Nat.add_succ, h₁] 
    
theorem add_commf (a b : ℕ) : a + b = b + a := by 
  induction b with 
  | zero => rw [Nat.zero_add]; rw [Nat.add_zero]
  | succ b h₁ => rw [Nat.add_succ]; rw [h₁]; rw [Nat.succ_add]

theorem fadd_assoc (a b c : ℕ) : a + b + c = a + (b + c) := by
  induction c with
  | zero => rw [Nat.add_zero]; rw [Nat.add_zero]
  | succ c h => rw [Nat.add_succ]; rw [Nat.add_succ]; rw [h]; rw [← Nat.add_succ]

theorem fadd_right_comm (a b c : ℕ) : a + b + c = a + c + b := by
   rw [Nat.add_assoc]
   rw [Nat.add_assoc]
   rw [Nat.add_comm b c]



  


end NaturalNumbersGame

#check Nat.le_trans


