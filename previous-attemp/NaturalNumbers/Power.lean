/-
# power game 

-/


import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

namespace NaturalNumbersGame

lemma pow_zero(m : ℕ) : m ^ 0 = 1 := by rfl

theorem zero_pow_zero : (0 : ℕ) ^ 0 = 1 := by
  rw [pow_zero]

lemma pow_succ(m n : ℕ) : m ^ Nat.succ n = m ^ n * m := by
  rfl

theorem zero_pow_succ (m : ℕ) : (0 : ℕ) ^ (Nat.succ m) = 0 := by
  rw [pow_succ]
  rw [mul_zero]

theorem pow_one (a : ℕ) : a ^ 1 = a := by
 sorry

end NaturalNumbersGame



