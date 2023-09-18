import Mathlib

open Real

/- # `#eval` and `#check` -/

/- Lean can compute -/
#eval 2 ^ 3 + 4 * 5 - 6

/- In Lean, every expression has a type, and `#check` can tell you the type -/

#check 2
#check 17 + 4
#check π
#check rexp 2

/- Every expression has a unique type -/

#check 2
#check (2 : ℕ)
#check (2 : ℤ)
#check (2 : ℚ)
#check (2 : ℝ)
#check (2 : ℂ)

/- Types are expressions too! -/

#check ℕ
#check ℝ

/- We can also make our own expressions, and give them names -/
def myFavouriteNumber : ℕ := 37

/- # Prop -/

/- The type `Prop` contains all statements

Unfortunate clash in terminology:
* In math: "Proposition" means
    useful proven statement (less important than a theorem)
* In logic: "Proposition" means
    any statement that can be either true or false.
-/

#check 2 + 2 = 4
#check rexp 1 < π
#check 2 + 2 = 5
#check Irrational (rexp 1 + π)

def MyDifficultStatement : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2)
def MyEasyFalseStatement : Prop := ∀ n : ℕ, ∃ p, n ≤ p ∧ Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)
def MyVeryEasyTrueStatement : Prop := ∀ n : ℕ, ∃ p, n ≤ p

/- If `p : Prop`, an expression of type `p` is a proof of `p`. -/

#check Eq.refl 4
example : 4 = 4 := by rfl
example : 2 + 2 = 4 := by rfl
example : 2 + 2 ≠ 5 := by simp

/- # Rewriting

Rewriting is a tactic that changes a part of a goal to something equal to it.

Here the commutator of two elements of a group is defined as
`⁅g, h⁆ =g * h * g ⁻¹ * h ⁻¹`
-/

variable (G : Type) [Group G] (g h : G)

#check commutatorElement_def g h
#check mul_inv_rev g h

lemma inverse_of_a_commutator : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by sorry

/-
Variants of `rw`:
* `rw [← my_lemma]` to rewrite `my_lemma` from right to left
* `rw [my_lemma] at h` to rewrite using `my_lemma` at `h`.
You have to know what lemma you need to rewrite with. `rw?` suggests possible rewrites
-/


/-
# Calculational proofs using `calc`
-/

example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by
  calc
    c = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring








/- There are more advanced tactics that will do some simple reasoning.
* `ring`: prove equalities in commutative rings
* `linarith`: prove linear (in)equalities -/

example (R : Type) [CommRing R] (a b : R) :
    (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring


example (a b c : ℝ) (h1 : 2 * a ≤ 3 * b) (h2 : 1 ≤ a) (h3 : c = 2) :
    c + a ≤ 5 * b := by linarith

/-
**Backwards reasoning** is where we chain implications backwards, deducing
what we want to prove from a combination of other statements (potentially even stronger ones).
-/

lemma simple_proof (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by sorry



#print simple_proof



/- We can prove the following manually, or using more advanced tactics. -/

example : Continuous (fun x ↦ 2 + x * rexp x) := by sorry

/- `apply?` -/



/-
# Difference between `rw` and `apply`
- `rw` can take place almost anywhere in the goal, but `apply` has to match the outermost thing you are trying to prove
- *generally* you `rw` with an equality, and `apply` anything else.
-/



/- ## Lemma naming
https://leanprover-community.github.io/contribute/naming.html
-/
