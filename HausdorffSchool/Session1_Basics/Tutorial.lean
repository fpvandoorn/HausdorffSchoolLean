import Mathlib

open Real

/- # `#eval` and `#check` -/

/- Lean can compute -/
#eval 2 ^ 3 + 4 * 5 - 6

/- In Lean, every expression has a type, and `#check` can tell you the type -/

#check 2
#check 17 + 4
#check π -- type using \pi
#check rexp 2

#check fun (x : ℝ) ↦ x ^ 2

/- Every expression has a unique type -/

#check 2
#check (2 : ℕ)
#check (2 : ℤ)
#check (2 : ℚ)
#check (2 : ℝ)
#check (2 : ℂ)



/- Warning: division on `ℕ` is division rounded down. -/

#eval 6 / 4 -- ⌊ 6 / 4 ⌋
#eval (6 : ℚ) / 4


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

def MyDifficultStatement : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2)

def MyEasyFalseStatement : Prop :=
  ∀ n : ℕ, ∃ p ≥ n, Prime p ∧ Prime (p + 2) ∧ Prime (p + 4)

def MyVeryEasyTrueStatement : Prop :=
  ∀ n : ℕ, ∃ p, p ≥ n





/- If `p : Prop`, an expression of type `p` is a proof of `p`. -/

#check Eq.refl 4
example : 4 = 4 := by rfl
example : 2 + 2 = 4 := by rfl
example : 2 + 2 ≠ 5 := by simp
-- example : (3 : ℕ) ≠ fun (x : ℝ) ↦ x ^ 2 := sorry


/- # Rewriting

`rw` (short for "rewrite") is a tactic that changes a part of a goal to something equal to it.

In the following lemma the commutator of two elements of a group is defined as
`⁅g, h⁆ =g * h * g ⁻¹ * h ⁻¹`
-/

variable {G : Type} [Group G] (g h : G)

#check commutatorElement_def g h
#check mul_inv_rev g h

lemma inverse_of_a_commutator : ⁅g, h⁆⁻¹ = ⁅h, g⁆ := by sorry

/-
Variants of `rw`:
* `rw [lemma1, lemma2, ...]` is short for multiple rewrites in a row
* `rw [← my_lemma]` to rewrite `my_lemma` from right to left
* `rw [my_lemma] at h` to rewrite using `my_lemma` at `h`.
You have to know what lemma you need to rewrite with. `rw?` suggests possible rewrites
-/

example (a b c d : ℝ) (h : c = a*d - 1) (h' : b = a*d) : c = b - 1 := by
  rw [← h'] at h
  exact h -- `rw [h]` also works


/-
# Calculational proofs using `calc`
-/

example (a b c d : ℝ) (h : a + c = b*a - d) (h' : d = a*b) : a + c = 0 := by
  calc a + c
      = b*a - d   := by rw [h]
    _ = b*a - a*b := by rw [h']
    _ = 0         := by ring








/- There are more advanced tactics that will do particular kinds of calculations.
* `ring`: prove equalities in commutative rings
* `linarith`: prove linear (in)equalities -/

variable {R : Type} [CommRing R] (a b : R)
example : (a - b) * (a + b) = a ^ 2 - b ^ 2 := by ring

example (a b c : ℝ) (h1 : 2 * a ≤ 3 * b) (h2 : 1 ≤ a) (h3 : c = 2) :
    c + a ≤ 5 * b := by linarith




/-
**Backwards reasoning** is where we chain implications backwards, deducing
what we want to prove from a combination of other statements (potentially even stronger ones).
-/

lemma simple_proof (p q r : Prop) (h1 : p → q) (h2 : q → r) : p → r := by sorry

-- #print simple_proof
-- #explode simple_proof


/- We can prove the following manually, or using more advanced tactics. -/

example : Continuous (fun x ↦ 2 + x * rexp x) := by sorry

/- `apply?` can give suggestions what lemmas you could apply. -/


/-
# Difference between `rw` and `apply`
- `rw` can take place almost anywhere in the goal, but `apply` has to match the outermost thing you are trying to prove
- *generally* you `rw` with an equality, and `apply` anything else.
-/




/- In the following lemma, notice that `a`, `b`, `c`
  are inside curly braces `{...}`.
  This means that these arguments are *implicit*:
  they don't have to be stated, but will be figured out by Lean automatically. -/

lemma my_lemma {a b c : ℝ} (h : a + b = a + c) : b = c :=
    add_left_cancel h

example {b c : ℝ} (h : 2 + b = 2 + c) : b = c := sorry -- prove using `my_lemma`






/- # Lemma naming
https://leanprover-community.github.io/contribute/naming.html
-/
