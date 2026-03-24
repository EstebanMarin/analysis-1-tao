/-
# Multiplication World

In this world, we'll prove fundamental properties of multiplication
on natural numbers.
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Tactic
import NaturalNumbers.Addition

namespace NaturalNumbersGame

/-
## Level 1: Multiplication by zero

Prove that multiplying by zero gives zero.
-/
lemma one_eq_succ_zero: 1 = Nat.succ 0 := by
  rfl
lemma mul_one (m : ℕ) : m * 1 = m := by 
  exact Nat.mul_one m

lemma mul_succ (a b : ℕ) : a * Nat.succ b = a * b + a  := by 
  exact Nat.mul_succ a b


theorem zero_mul (m : ℕ) : 0 * m = 0 := by
  induction m with
  | zero => rw [mul_zero]
  | succ a h₁ => rw [mul_succ]; rw[h₁]

theorem succ_mul (a b : ℕ) : Nat.succ a * b = a * b + b := by
  induction b with
  | zero => 
    rw [mul_zero]; 
    rw[mul_zero]; 
    rfl
  | succ a h₁ => 
    rw [Nat.add_one_mul]


theorem mul_comm (a b : ℕ) : a * b = b * a := by
  induction b with 
  | zero => 
    rw[Nat.mul_comm]
  | succ a h₁ =>
    rw [add_one_mul];
    rw [←h₁];
    rfl;

theorem one_mul (m : ℕ): 1 * m = m := by
  induction m with
  | zero => rw [mul_zero]
  | succ a h₁ => rw [Nat.one_mul]


theorem two_mul (m : ℕ): 2 * m = m + m := by
  induction m with 
  | zero => rw[add_zero]
  | succ n h₁ => rw [succ_mul, one_mul]

theorem mul_add (a b c : ℕ) : a * (b + c) = a * b + a * c := by
  induction c with 
  | zero => 
    rw [add_zero]
    rw [mul_zero]
    rw [add_zero]
  | succ a h₁ => 
    rw [Nat.left_distrib]

theorem add_mul (a b c : ℕ) : (a + b) * c = a * c + b * c := by 
  rw [mul_comm]; 
  rw [mul_add]; 
  rw [mul_comm]; 
  rw [mul_comm b c]

theorem mul_assoc (a b c : ℕ) : (a * b) * c = a * (b * c) := by
  induction c with 
  | zero => rw [mul_zero]; rw [mul_zero]; rw [mul_zero]
  | succ c h₁ => rw [Nat.mul_assoc]

end NaturalNumbersGame
  
