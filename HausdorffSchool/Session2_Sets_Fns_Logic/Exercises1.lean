import HausdorffSchool.Common
import Mathlib.Data.Real.Basic

open Function

example (p q r : Prop) : (p → q) → (p → r) → p → q := by {
  sorry
}

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by {
  sorry
}

example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) := by {
  sorry
}

example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p := by {
  sorry
}

example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y := by {
  sorry
}

example (α : Type) (p q : α → Prop) :
    (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := by {
  sorry
}

example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := by {
  sorry
}

example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := by {
  sorry
}

example (α : Type) (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := by {
  sorry
}

example (α : Type) (p : α → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := by {
  push_neg at h
  sorry
}

example (α : Type) (p : α → Prop) (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := by {
  sorry
}

example (p q q' : Prop) (h : p ∧ q) (hq : q → q') : p ∧ q' := by {
  sorry
}

example (p : Prop) (h : p ∨ p) : p := by {
  sorry
}

example (α : Type) (p : α → Prop) (q : Prop) (h : ∃ x, p x ∨ q) : (∃ x, p x) ∨ q := by {
  sorry
}

example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := by {
  sorry
}

section
variable (f g : ℝ → ℝ)

/-
Hints:
* `Monotone` is
  ```
  def Monotone (f : α → β) : Prop := ∀ a b, a ≤ b → f a ≤ f b
  ```
  and so `intro` applies to it.
* `dsimp` can simplify `(fun x => ...) a` applications
  (so can `beta_reduce`)
* the lemma `add_le_add : a ≤ b → c ≤ d → a + c ≤ b + d` might be useful,
  or `gcongr` applies to inequalities and tries to match things up
-/
example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f x + g x := by {
  sorry
}

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by {
  sorry
}

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by {
  sorry
}

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by {
  sorry
}

section
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- Hint: right click on Surjective and click "Go to definition"
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by {
  sorry
}
end

example {c : ℝ} : Surjective fun x ↦ x + c := by {
  intro x
  use x - c
  dsimp
  ring
}

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by {
  sorry
}

end
