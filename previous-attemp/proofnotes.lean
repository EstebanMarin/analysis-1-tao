import Mathlib

namespace Nat

example (n : ℕ) : n = n := rfl

example (P Q : Prop) (h : P ∧ Q) : Q ∧ P := by
  exact And.comm.mp h

example (n : ℕ) (h : 2026 < n) : 4 < n := lt_trans (by decide) h

example : ∀ x : ℕ, x = x := by
  intro x
  rfl

example (a b : ℕ) (h₁ : a = 1) (h₂ : a = b) : b = 1 := by
  symm
  rwa [h₁] at h₂

example : (fun (x : ℕ) ↦ x + 1 - 1) = id := by
  ext x
  rfl

example (P Q : Prop) (h : P → Q) (p : P) : Q := by
  apply h
  exact p

example : (∀ n > 2016, n > 4) ∧ (5 ≠ 20 - 2 ∨ 4 = 5) ∧ ({1} = {x | x = 1}) := by
  refine ⟨fun n h ↦ ?_, ?_, ?_⟩
  · exact lt_trans (by decide) h
  · decide
  · rfl

example (n : ℕ) (h : ∃ x : ℕ, x ∣ n ∧ 1 < x ∧ x < n) : ¬ n.Prime := by
  obtain ⟨x, h₁, h₂, h₃⟩ := h
  exact not_prime_of_dvd_of_lt h₁ h₂ h₃

example (α) (f : α → α) (h : ∀ g : α → α, f ≠ g → f ∘ g ∘ f ≠ g ∘ f ∘ g) :
    ∀ g, f ∘ g ∘ f = g ∘ f ∘ g → f = g := by
  intro g hg
  have : ¬ f ∘ g ∘ f ≠ g ∘ f ∘ g → ¬ f ≠ g := by
    intro hf
    exact Not.imp hf (h g)
  rw [ne_eq, not_not, ne_eq, not_not] at this
  apply this
  exact hg

lemma le_square (n : ℕ) : n ≤ n^2 := by
  induction n with
  | zero => decide
  | succ n ih =>
    have : (n + 1) ^ 2 = n ^ 2 + 2 * n + 1 := by
      rw [pow_two, mul_add, add_mul, pow_two]
      omega
    rw [this, add_assoc]
    apply Nat.add_le_add
    · exact ih
    · exact le_add_left 1 (2 * n)

theorem sum_of_first_n (n : ℕ) : (∑ i ∈ Finset.range n, i) = n * (n - 1) / 2 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [add_tsub_cancel_right]
    have : (n + 1) * n / 2 =  n * (n - 1) / 2 + n := by
      have : n = 2 * n / 2 := by omega
      nth_rw 5 [this]
      have : n * (n - 1) / 2 + 2 * n / 2 = (n * (n - 1) + 2 * n) / 2 := by omega
      rw [this]
      have : (n + 1) * n = n * (n - 1) + 2 * n := by
        rw [add_mul, Nat.mul_sub, one_mul, mul_one, two_mul, ← Nat.add_assoc (n * n - n) n n,
          Nat.sub_add_cancel]
        rw [← pow_two]
        exact le_square n
      rw [this]
    rw [this, ← ih, Finset.sum_range_succ (fun x ↦ x) n]

example (a b c d : ℕ) (h₁ : a ≤ b) (h₂ : b < c) (h₃ : c ≤ d) : a < d :=
  sorry

end Nat

namespace List

variable {α} [LinearOrder α]

lemma list_reverse_maximum (l : List α) :
    l.reverse.maximum = l.maximum := by
  sorry

lemma Perm.maximum_eq {l l' : List α} (h : l ~ l') :
    l.maximum = l'.maximum := by
  sorry

lemma list_reverse_maximum' (l : List α) :
    l.reverse.maximum = l.maximum :=
  sorry

end List
