import HausdorffSchool.Common
import Mathlib.Data.Real.Basic

open Function

example (p q r : Prop) : (p → q) → (p → r) → p → q := by {
  intros hpq _hpr
  exact hpq
}

example (p q r : Prop) (hpq : p → q) (hqr : q → r) : p → r := by {
  intro hp
  apply hqr
  apply hpq
  exact hp
}

example (p q r s : Prop) : (p → (q → r)) → (p → (r → s)) → (p → (q → s)) := by {
  intros hqr hrs hp hq
  apply hrs hp
  exact hqr hp hq
}

example (p q : Prop) : (p → q) → (p → ¬ q) → ¬ p := by {
  intros hpq hpnq hp
  specialize hpq hp
  specialize hpnq hp
  exact hpnq hpq
}

example (α β : Type) (p : α → β → Prop) : (∀ x y, p x y) → ∀ y x, p x y := by {
  intros h y x
  exact h x y
}

example (α : Type) (p q : α → Prop) :
    (∀ x, p x) → (∀ x, p x → q x) → ∀ x, q x := by {
  intros hp hpq x
  exact hpq x (hp x)
}

example (α β : Type) (p : α → β → Prop) (h : ∃ x, ∀ y, p x y) : ∀ y, ∃ x, p x y := by {
  intro y
  obtain ⟨x, h'⟩ := h
  use x, h' y  
}

example (α : Type) (p : α → Prop) (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := by {
  intro ⟨x, hx⟩
  exact h x hx  
}

example (α : Type) (p : α → Prop) (h : ∃ x, ¬ p x) : ¬ ∀ x, p x := by {
  obtain ⟨x, h'⟩ := h
  intro h
  exact h' (h x)
}

example (α : Type) (p : α → Prop) (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := by {
  push_neg at h
  assumption
}

example (α : Type) (p : α → Prop) (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := by {
  intro x hp
  apply h
  use x, hp
}

example (p q q' : Prop) (h : p ∧ q) (hq : q → q') : p ∧ q' := by {
  constructor
  · exact h.1
  · exact hq h.2 
}


example (p : Prop) (h : p ∨ p) : p := by {
  obtain (hp | hp) := h
  · exact hp
  · exact hp
}

example (α : Type) (p : α → Prop) (q : Prop) (h : ∃ x, p x ∨ q) : (∃ x, p x) ∨ q := by {
  obtain ⟨x, (hx | hq)⟩ := h
  · left
    exact ⟨x, hx⟩
  · right
    exact hq  
}

example (p q r : Prop) (hpq : p ↔ q) (hqr : q ↔ r) : p ↔ r := by {
  rw [hpq, hqr]
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
  intro x y hxy
  dsimp
  gcongr
  · exact mf hxy
  · exact mg hxy 
}

example {c : ℝ} (mf : Monotone f) (nnc : 0 ≤ c) : Monotone fun x ↦ c * f x := by {
  intro x y hxy
  dsimp
  gcongr
  exact mf hxy
}

example (mf : Monotone f) (mg : Monotone g) : Monotone fun x ↦ f (g x) := by {
  intro x y hxy
  dsimp
  apply mf
  apply mg
  exact hxy
}

example : ∃ x : ℝ, 2 < x ∧ x < 3 := by {
  use 2 + 1/2
  norm_num
}

section
variable {α : Type*} {β : Type*} {γ : Type*}
variable {g : β → γ} {f : α → β}

-- Hint: right click on Surjective and click "Go to definition"
example (surjg : Surjective g) (surjf : Surjective f) : Surjective fun x ↦ g (f x) := by {
  intro c
  obtain ⟨b, h⟩ := surjg c
  obtain ⟨a, h'⟩ := surjf b
  subst_vars -- eliminates h and h'. can also use `rw`, etc. here
  use a
}

end

example {c : ℝ} : Surjective fun x ↦ x + c := by {
  intro x
  use x - c
  dsimp
  ring
}

example {c : ℝ} (h : c ≠ 0) : Surjective fun x ↦ c * x := by {
  intro x
  use x/c
  dsimp
  rw [mul_div_cancel' _ h]
  -- or field_simp; ring
}

end
