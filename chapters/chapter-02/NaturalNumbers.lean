import Mathlib.Tactic

/-!
# Chapter 2: Starting at the Beginning - The Natural Numbers
## Section 2.1: The Peano Axioms

Based on Terence Tao's Analysis I, Chapter 2.
-/

namespace Chapter2

-- Define our own natural numbers from scratch
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr, DecidableEq

-- Axiom 2.1: 0 is a natural number
instance Nat.instZero : Zero Nat := ⟨Nat.zero⟩

-- Axiom 2.2: Successor function (using ++ notation)
postfix:max "++" => Nat.succ

-- Define numerals 1, 2, 3, etc.
instance Nat.instOfNat {n : _root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ m => m++) n

instance Nat.instOne : One Nat := ⟨1⟩

-- Axiom 2.3: 0 is not the successor of any natural number
theorem Nat.succ_ne_zero (n : Nat) : n++ ≠ 0 := by
  intro h
  injection h

-- Axiom 2.4: Successor is injective
theorem Nat.succ_inj {n m : Nat} (h : n++ = m++) : n = m := by
  injection h

-- Axiom 2.5: Principle of Mathematical Induction
theorem Nat.induction {P : Nat → Prop}
    (base : P 0)
    (ind : ∀ n, P n → P n++) :
    ∀ n, P n := by
  intro n
  induction n with
  | zero => exact base
  | succ n ih => exact ind n ih

end Chapter2
