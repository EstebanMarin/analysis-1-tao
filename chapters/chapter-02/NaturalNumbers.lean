import Mathlib.Tactic

/-!
# Chapter 2: Starting at the Beginning - The Natural Numbers

**A Complete Journey Through the Foundations**

This file covers **all of Chapter 2** from Terence Tao's Analysis I:
- Section 2.1: The Peano Axioms
- Section 2.2: Addition
- Section 2.3: Multiplication

All numbering refers to the original text.

## Reference
- Book: Terence Tao, Analysis I (Third Edition)
- Online: https://teorth.github.io/analysis/

-/

namespace Chapter2

/-! # SECTION 2.1: THE PEANO AXIOMS -/

/-!
## The Story Begins: What Are Numbers?

We start at the very beginning: constructing natural numbers from scratch using only
logic and the **Peano axioms**.
n-/

inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
deriving Repr, DecidableEq

/-- Axiom 2.1: 0 is a natural number -/
instance Nat.instZero : Zero Nat := ⟨Nat.zero⟩

#check 0

/-- Axiom 2.2: Successor function
  postfix:max "++" => Nat.succ — declares a notation (syntactic sugar).

  - postfix — the operator goes after its argument. As opposed to prefix
  (before) or infix (between two args).
  - :max — the precedence level. max is the highest possible precedence, meaning
   ++ binds tighter than anything. So n + 1++ parses as n + (1++), not (n +
  1)++.
  - "++" — the literal symbol you type.
  - => Nat.succ — what it expands to. Nat.succ is the successor constructor of
  Nat.

  ---
  What it reads in plain English

  ▎ "Let n++ be notation for Nat.succ n."

  So after this declaration:

  0++      -- means Nat.succ 0  (i.e., 1)
  0++++    -- means Nat.succ (Nat.succ 0)  (i.e., 2)

 -/
postfix:max "++" => Nat.succ      

/-- Definition 2.1.3: Numerals 
Some times you just need to skim through the syntax and understand the singleton idea.
-/

instance Nat.instOfNat {n : _root_.Nat} : OfNat Nat n where
  ofNat := _root_.Nat.rec 0 (fun _ m ↦ m++) n

/--   _root_.Nat.rec 0 (fun _ m => m++) n

  This is primitive recursion on n. Nat.rec has the shape:

  Nat.rec (base) (step) (target)

  ┌────────┬────────────────┬──────────────────────────────────────────────────────────┐
  │  Part  │     Value      │                         Meaning                          │
  ├────────┼────────────────┼──────────────────────────────────────────────────────────┤
  │ base   │ 0              │ when n = 0, return 0                                     │
  ├────────┼────────────────┼──────────────────────────────────────────────────────────┤
  │ step   │ fun _ m => m++ │ when n = succ k, take the previous result m and apply ++ │
  ├────────┼────────────────┼──────────────────────────────────────────────────────────┤
  │ target │ n              │ the number to recurse on                                 │
  └────────┴────────────────┴──────────────────────────────────────────────────────────┘

  So it counts up from 0 by applying ++ exactly n times:

  3  →  0++ ++ ++   →  Nat.succ (Nat.succ (Nat.succ 0))

-/
instance Nat.instOne : One Nat := ⟨1⟩
/-- All we are really saying here is that -/
example : (1 : Nat) = Nat.succ 0 := by rfl
example : (1 : Nat) = 0++ := by rfl

example : (2 : Nat) = (0++)++ := by rfl

/-- Definition 2.1.4 3 is a natural number -/

example : (0++++++) = 3 := by rfl 
example : (2++) = 3 := by rfl
example : (1++) = 2 := by rfl
example : 2 = Nat.succ (Nat.succ 0) := by rfl
example : 1 = Nat.succ 0 := by rfl

/-- proposition 2.1.6 4 is not equal to 0 
 What 4 actually is

  4 = Nat.succ 3
    = Nat.succ (Nat.succ 2)
    = Nat.succ (Nat.succ (Nat.succ 1))
    = Nat.succ (Nat.succ (Nat.succ (Nat.succ 0)))

  So h₁ : 4 = 0 is really:
  h₁ : Nat.succ (Nat.succ (Nat.succ (Nat.succ 0))) = Nat.zero

  ---
  What injection does

  It looks at the outermost constructors:
  - Left side: Nat.succ (...)
  - Right side: Nat.zero

  Different constructors → immediate contradiction → goal closed.
-/
theorem Nat.four_ne_zero: 4 ≠ 0 := by
  intro h₁
  injection h₁



/-- Axiom 2.3: 0 is not a successor 
To avoid wrap-around issue lets say
-/
theorem Nat.succ_ne_zero (n: Nat): n++ ≠ 0 := by
  intro h₁
  injection h₁


/-- Axiom 2.4: Successor is injective
 What happens step by step

  You have:
  h : n++ = m++
  -- which is:
  h : Nat.succ n = Nat.succ m

  injection h looks at h and says:

  ▎ "Both sides use the same constructor Nat.succ. Since constructors are injective, the arguments must be equal."

  It automatically produces a new hypothesis:
  h' : n = m

  And since that's exactly your goal, the proof is complete.

 
  ---
  The mental model

  injection just peels off the outer constructor:

  Nat.succ n = Nat.succ m
           ↓ injection
           n = m
 -/

theorem Nat.succ_inj {n m : Nat} (h : n++ = m++) : n = m := by
  injection h

/-- Axiom 2.5: Mathematical Induction -/
theorem Nat.induction {P : Nat → Prop}
  (h₀: P 0) 
  (h₁: ∀ n, P n → P (n++)):
  ∀ n, P n := by
    intro n 
    induction n with 
      | zero => exact h₀
      | succ n α => exact h₁ n α 


/-- Recursion principle for defining functions -/
abbrev Nat.recurse (f : Nat → Nat → Nat) (c : Nat) : Nat → Nat :=
  fun n ↦ match n with
  | 0 => c
  | n++ => f n (recurse f c n)

theorem Nat.recurse_zero (f : Nat → Nat → Nat) (c : Nat) :
    Nat.recurse f c 0 = c := by rfl

theorem Nat.recurse_succ (f : Nat → Nat → Nat) (c : Nat) (n : Nat) :
    recurse f c (n++) = f n (recurse f c n) := by rfl


/-! # SECTION 2.2: ADDITION -/

/-!
## Building Addition from Scratch

Now comes the exciting part: defining addition!

We can't just assume addition exists - we must **define** it using recursion.

**Definition 2.2.1:** For any natural number m, we define 0 + m = m.
For any n, we define (n++) + m = (n + m)++.

Think about this:
- 0 + 3 = 3 (by definition)
- 1 + 3 = (0++) + 3 = (0 + 3)++ = 3++ = 4
- 2 + 3 = (1++) + 3 = (1 + 3)++ = 4++ = 5

We're literally counting up by repeatedly applying successor!
-/

/--
Definition 2.2.1: Addition of natural numbers.

We use recursion on the first argument:
- Base case: 0 + m = m
- Recursive case: (n++) + m = (n + m)++
-/
abbrev Nat.add (n m : Nat) : Nat := Nat.recurse (fun _ sum => sum++) m n

instance Nat.instAdd : Add Nat where
  add := add

/-!
## Lemma 2.2.2: n + 0 = n

**Our first non-trivial proof about addition!**

This seems obvious: adding zero shouldn't change anything. But we must prove it
using our axioms and definition.

**Proof by induction on n:**

*Base case (n = 0):*
- We need: 0 + 0 = 0
- By definition of addition: 0 + 0 = 0 ✓

*Inductive step:* Assume n + 0 = n, prove (n++) + 0 = n++
- By definition: (n++) + 0 = (n + 0)++
- By inductive hypothesis: = n++  ✓

By induction, n + 0 = n for all n. ∎
-/

@[simp]
theorem Nat.zero_add (m : Nat) : 0 + m = m := by
  -- By definition of addition
  rfl

theorem Nat.succ_add (n m : Nat) : n++ + m = (n + m)++ := by
  -- By definition of addition
  rfl

@[simp]
lemma Nat.add_zero (n : Nat) : n + 0 = n := by
  -- Prove by induction on n
  revert n
  apply induction
  · -- Base case: 0 + 0 = 0
    exact zero_add 0
  · -- Inductive step: assume n + 0 = n, prove (n++) + 0 = n++
    intro n ih
    calc
      (n++) + 0 = (n + 0)++ := by rfl  -- definition of addition
      _ = n++ := by rw [ih]            -- inductive hypothesis

/-!
## Lemma 2.2.3: n + (m++) = (n + m)++

**Adding a successor**

This says: adding the successor of m is the same as adding m and then taking successor.

This is KEY for proving commutativity!
-/

lemma Nat.add_succ (n m : Nat) : n + (m++) = (n + m)++ := by
  -- Prove by induction on n
  revert n
  apply induction
  · -- Base case: 0 + (m++) = (0 + m)++
    calc
      0 + (m++) = m++ := by rw [zero_add]        -- definition
      _ = (0 + m)++ := by rw [zero_add]
  · -- Inductive step: assume n + (m++) = (n + m)++, prove (n++) + (m++) = ((n++) + m)++
    intro n ih
    calc
      (n++) + (m++) = (n + (m++))++ := by rfl      -- definition
      _ = ((n + m)++)++ := by rw [ih]              -- inductive hypothesis
      _ = ((n++) + m)++ := by rfl                  -- definition

/-!
## Proposition 2.2.4: Addition is commutative

**The Big One: m + n = n + m**

This is NOT obvious from our definition! We defined addition recursively on the first
argument, so 3 + 2 and 2 + 3 are computed completely differently.

**Proof:** By induction on n.

*Base case:* m + 0 = 0 + m
- LHS: m + 0 = m (by Lemma 2.2.2)
- RHS: 0 + m = m (by definition)
- So LHS = RHS ✓

*Inductive step:* Assume m + n = n + m, prove m + (n++) = (n++) + m
- LHS: m + (n++) = (m + n)++ (by Lemma 2.2.3)
-      = (n + m)++ (by inductive hypothesis)
- RHS: (n++) + m = (n + m)++ (by definition)
- So LHS = RHS ✓

By induction, addition is commutative! ∎
-/

theorem Nat.add_comm (n m : Nat) : n + m = m + n := by
  -- Prove by induction on m
  revert m
  apply induction
  · -- Base case: n + 0 = 0 + n
    rw [add_zero, zero_add]
  · -- Inductive step: assume n + m = m + n, prove n + (m++) = (m++) + n
    intro m ih
    calc
      n + (m++) = (n + m)++ := by rw [add_succ]    -- Lemma 2.2.3
      _ = (m + n)++ := by rw [ih]                   -- inductive hypothesis
      _ = (m++) + n := by rfl                       -- definition

/-!
## Proposition 2.2.5: Addition is associative

**(a + b) + c = a + (b + c)**

Order of parentheses doesn't matter!
-/

theorem Nat.add_assoc (a b c : Nat) : (a + b) + c = a + (b + c) := by
  -- Prove by induction on a
  revert a
  apply induction
  · -- Base case: (0 + b) + c = 0 + (b + c)
    rw [zero_add, zero_add]
  · -- Inductive step
    intro a ih
    calc
      ((a++) + b) + c = ((a + b)++) + c := by rfl
      _ = ((a + b) + c)++ := by rfl
      _ = (a + (b + c))++ := by rw [ih]
      _ = (a++) + (b + c) := by rfl

/-!
## Example: 2 + 3 = 5

Let's actually compute an example to see our definition in action!
-/

example : (2 : Nat) + 3 = 5 := by
  -- Expand definitions step by step
  calc
    (2 : Nat) + 3 = 1++ + 3 := by rfl
    _ = (1 + 3)++ := by rfl
    _ = (0++ + 3)++ := by rfl
    _ = ((0 + 3)++)++ := by rfl
    _ = (3++)++ := by rfl
    _ = 4++ := by rfl
    _ = 5 := by rfl

/-! # SECTION 2.3: MULTIPLICATION -/

/-!
## Building Multiplication from Addition

Just as we built addition from successor, we now build multiplication from addition!

**Definition 2.3.1:** For any natural number m, we define 0 × m = 0.
For any n, we define (n++) × m = (n × m) + m.

Think about this:
- 0 × 3 = 0 (by definition)
- 1 × 3 = (0++) × 3 = (0 × 3) + 3 = 0 + 3 = 3
- 2 × 3 = (1++) × 3 = (1 × 3) + 3 = 3 + 3 = 6
- 3 × 3 = (2++) × 3 = (2 × 3) + 3 = 6 + 3 = 9

Multiplication is repeated addition!
-/

/--
Definition 2.3.1: Multiplication of natural numbers.

We use recursion on the first argument:
- Base case: 0 × m = 0
- Recursive case: (n++) × m = (n × m) + m
-/
abbrev Nat.mul (n m : Nat) : Nat := Nat.recurse (fun _ prod => prod + m) 0 n

instance Nat.instMul : Mul Nat where
  mul := mul

@[simp]
theorem Nat.zero_mul (m : Nat) : 0 * m = 0 := by
  -- By definition
  rfl

theorem Nat.succ_mul (n m : Nat) : (n++) * m = n * m + m := by
  -- By definition
  rfl

/-!
## Lemma 2.3.2: n × 0 = 0

**Anything times zero is zero**

Again, this requires proof! Our definition has 0 on the left, not the right.
-/

@[simp]
lemma Nat.mul_zero (n : Nat) : n * 0 = 0 := by
  -- Prove by induction on n
  revert n
  apply induction
  · -- Base case: 0 * 0 = 0
    rfl
  · -- Inductive step: assume n * 0 = 0, prove (n++) * 0 = 0
    intro n ih
    calc
      (n++) * 0 = n * 0 + 0 := by rfl   -- definition
      _ = 0 + 0 := by rw [ih]           -- inductive hypothesis
      _ = 0 := by rfl                   -- addition

/-!
## Lemma 2.3.3: n × (m++) = n × m + n

**Multiplying by a successor**

This is the multiplicative version of Lemma 2.2.3!
-/

lemma Nat.mul_succ (n m : Nat) : n * (m++) = n * m + n := by
  -- Prove by induction on n
  revert n
  apply induction
  · -- Base case: 0 * (m++) = 0 * m + 0
    simp
  · -- Inductive step
    intro n ih
    calc
      (n++) * (m++) = (n++) * m + (n++) := by rfl
      _ = (n * m + m) + (n++) := by rfl
      _ = (n * m + m) + n++ := by rfl
      _ = ((n * m) + (m + n))++ := by rw [add_assoc, add_assoc]
      _ = ((n * m) + (n + m))++ := by rw [add_comm m n]
      _ = (((n * m) + n) + m)++ := by rw [←add_assoc]
      _ = ((n * (m++)) + m)++ := by rw [←ih]
      _ = (n * (m++))++ + m := by rfl
      _ = (n++) * m + (n++) := by rfl

/-!
## Proposition 2.3.4: Multiplication is commutative

**m × n = n × m**

Just like addition, this requires careful proof by induction.
-/

theorem Nat.mul_comm (n m : Nat) : n * m = m * n := by
  revert m
  apply induction
  · -- Base case: n * 0 = 0 * n
    simp
  · -- Inductive step: assume n * m = m * n, prove n * (m++) = (m++) * n
    intro m ih
    calc
      n * (m++) = n * m + n := by rw [mul_succ]
      _ = m * n + n := by rw [ih]
      _ = (m++) * n := by rfl

/-!
## Distributivity: n × (m + k) = n × m + n × k

**Multiplication distributes over addition**

This connects our two operations!
-/

theorem Nat.mul_add (n m k : Nat) : n * (m + k) = n * m + n * k := by
  revert k
  apply induction
  · -- Base case: n * (m + 0) = n * m + n * 0
    simp
  · -- Inductive step
    intro k ih
    calc
      n * (m + (k++)) = n * ((m + k)++) := by rfl
      _ = n * (m + k) + n := by rw [mul_succ]
      _ = (n * m + n * k) + n := by rw [ih]
      _ = n * m + (n * k + n) := by rw [add_assoc]
      _ = n * m + n * (k++) := by rfl

/-!
## Proposition 2.3.5: Multiplication is associative

**(a × b) × c = a × (b × c)**
-/

theorem Nat.mul_assoc (a b c : Nat) : (a * b) * c = a * (b * c) := by
  revert a
  apply induction
  · -- Base case: (0 * b) * c = 0 * (b * c)
    simp
  · -- Inductive step
    intro a ih
    calc
      ((a++) * b) * c = (a * b + b) * c := by rfl
      _ = (a * b) * c + b * c := by rw [mul_add]
      _ = a * (b * c) + b * c := by rw [ih]
      _ = (a++) * (b * c) := by rfl

/-!
## Example: 2 × 3 = 6

Let's verify multiplication works:
-/

example : (2 : Nat) * 3 = 6 := by
  calc
    (2 : Nat) * 3 = 1++ * 3 := by rfl
    _ = 1 * 3 + 3 := by rfl
    _ = (0++ * 3) + 3 := by rfl
    _ = (0 * 3 + 3) + 3 := by rfl
    _ = (0 + 3) + 3 := by rfl
    _ = 3 + 3 := by rfl
    _ = 6 := by decide

/-!
## Summary: What We've Built

**Congratulations!** We've constructed arithmetic from scratch:

**Section 2.1 - Foundation:**
1. Natural numbers via Peano axioms
2. Induction principle
3. Recursive definitions

**Section 2.2 - Addition:**
1. Defined addition recursively
2. Proved: n + 0 = 0 + n = n
3. Proved: addition is commutative and associative

**Section 2.3 - Multiplication:**
1. Defined multiplication as repeated addition
2. Proved: n × 0 = 0 × n = 0
3. Proved: multiplication is commutative and associative
4. Proved: distributive law

**Key Insight:** Every property we "know" about arithmetic must be proven from first
principles. Nothing is taken for granted!

## What's Next?

In Chapter 3, we'll tackle:
- Set theory foundations
- Russell's paradox (why naive set theory fails)
- Functions and relations
- Cardinality

The journey continues deeper! 🚀
-/

end Chapter2
