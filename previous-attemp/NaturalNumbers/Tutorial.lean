/-
# Tutorial World

Welcome to the Natural Numbers Game!

In this tutorial world, you'll learn the basic tactics needed to prove
theorems about natural numbers using mathlib's Nat type.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
## Level 1: The `rfl` tactic

The `rfl` tactic proves goals of the form `x = x`.
It also works when both sides are definitionally equal.

Let's prove that 2 + 2 = 4.
-/

example : 2 + 2 = 4 := by
  rfl

/-
## Level 2: The `rw` tactic

The `rw` (rewrite) tactic is used to substitute one thing for another.
If you have a hypothesis `h : a = b`, then `rw [h]` will replace all
occurrences of `a` with `b` in the goal.
-/

theorem tutorial_level_2 (x y : ℕ) (h₁ : x = y) : x + 0 = y := by
  rw [h₁]
  rfl

/-
## Level 3: Using library lemmas

Mathlib has many lemmas about natural numbers.
For example, `Nat.add_zero` says that `n + 0 = n`.
-/

theorem tutorial_level_3 (n : ℕ) : n + 0 = n := by
  rfl

/-
## Level 4: The `exact` tactic

If we have a hypothesis that exactly matches the goal,
we can use the `exact` tactic.
-/

theorem tutorial_level_4 (a b : ℕ) (h : a = b) : a = b := by
  exact h

/-
## Level 5: Multiple rewrites

We can chain multiple rewrites together.
-/

theorem tutorial_level_5 (a b c : ℕ) (h1 : a = b) (h2 : b = c) : a = c := by
  rw [h1]
  rw [h2]

/-
## Exercises: Try these yourself!

Remove the `sorry` and replace with your proof.
-/

-- Exercise 1: Prove using rfl
theorem exercise_1 : 5 + 3 = 8 := by
  rfl

-- Exercise 2: Use Nat.add_zero
theorem exercise_2 (x : ℕ) : x + 0 = x := by
  rw [Nat.add_zero]

theorem rwtactic (x y: ℕ) (h: y = x + 7): 2 * y = 2 * (x + 7) := by
  rw [h]

-- Exercise 3: Chain hypotheses
theorem exercise_3 (x y z : ℕ) (h1 : x = y) (h2 : y = z) : x = z := by
  rw [h1]
  rw [h2]

-- Exercise 4: Combine tactics
--theorem exercise_4 (a b : ℕ) (h : a = b) : a + 0 = b := by
--  sorry

theorem rlfTactic (a b: ℕ): 37 * a + b = 37 * a + b := by
  rfl

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/2

theorem level2 (a b: ℕ)(h: a = b + 7): 2 * a = 2 * (b + 7) := by
  rw [h]

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/3

lemma one_eq_succ_zero: 1 = Nat.succ 0 := by
  rfl

lemma two_eq_succ_one: 2 = Nat.succ 1 := by
  rfl

theorem two_number_after_after_zero: 2 = Nat.succ (Nat.succ 0) := by
  rw [two_eq_succ_one]

theorem two_number_after_after_zero_backwards: 2 = Nat.succ (Nat.succ 0) := by
  rw [← one_eq_succ_zero]

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/5

lemma add_zeroMine(a: ℕ): a + 0 = a := by
  rfl

theorem level5Theorem (a b c: ℕ): a + (b + 0) + (c + 0) =  a + b + c := by
  rw [add_zeroMine]
  rw [Nat.add_zero]

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/6

-- precission rewriting

theorem level6Theorem (a b c: ℕ): a + (b + 0) + (c + 0) =  a + b + c := by
  rw [add_zeroMine c]
  rw [Nat.add_zero b]

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/7

lemma myadd_succ (a b : ℕ): a + Nat.succ b = Nat.succ (a + b) := by
  rfl

theorem succ_eq_add_one(a: ℕ): Nat.succ a = a + 1 := by
  rw [one_eq_succ_zero]

-- https://adam.math.hhu.de/#/g/leanprover-community/nng4/world/Tutorial/level/8

theorem twoplustwo: 2 + 2 = 4 := by
  --nth_rewrite 2 [two_eq_succ_one]
  --rw [Nat.add_succ]

  nth_rewrite 2 [two_eq_succ_one]
  rw [myadd_succ]
  --rw [one_eq_succ_zero]
  --rw [Nat.add_succ]
  --rw [Nat.add_zero]
  --rfl

-- nth_rewrite 2 [two_eq_succ_one] -- only change the second `2` to `succ 1`.
-- rw [add_succ]
-- rw [one_eq_succ_zero]
-- rw [add_succ, add_zero] -- two rewrites at once
-- rw [← three_eq_succ_two] -- change `succ 2` to `3`
-- rw [← four_eq_succ_three]
-- rfl

-- addition world

  
-- https://lean-lang.org/theorem_proving_in_lean4/Propositions-and-Proofs/#propositions-and-proofs

#check And
#check Not

axiom and_commut: ∀ p q: Prop, p ∧ q → q ∧ p  

variable (p q : Prop)

#check and_commut p q

axiom modus_ponens:
  ∀ p q: Prop,
  (p → q) → p → q

#check modus_ponens
