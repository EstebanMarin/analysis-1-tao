import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

inductive MyNat: Type where 
  | zero : MyNat 
  | succ : MyNat → MyNat

inductive AExp: Type where
  | num: ℤ → AExp
  | var: String → AExp
  | add: AExp → AExp → AExp
  | sub: AExp → AExp → AExp
  | mul: AExp → AExp → AExp
  | div: AExp → AExp → AExpd

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

#check MyList.cons

def add: ℕ → ℕ → ℕ
  | m, Nat.zero => m
  | m, Nat.succ n => Nat.succ (add m n)


#eval add 2 7 

#reduce add 2 7

def mul: ℕ → ℕ → ℕ 
  | _, Nat.zero =>  Nat.zero
  | m, Nat.succ n => add m (mul m n)

def power: ℕ → ℕ → ℕ 
  | _, Nat.zero => 1
  | m, Nat.succ n => mul m (power m n)


-- chapter 3

theorem fst_of_two_props:
  ∀ a b: Prop, a → b → a :=  by 
    intro a b h₁ h₂
    apply h₁ 
