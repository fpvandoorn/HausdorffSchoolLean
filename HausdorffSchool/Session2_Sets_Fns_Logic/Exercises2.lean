import HausdorffSchool.Common
import Mathlib.Data.Set.Basic

open Set Function

section
variable {α β : Type*} (s t u : Set α)

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by {
  sorry
}

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by {
  sorry
}

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by {
  sorry
}

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by {
  sorry
}

example : s ∩ t = t ∩ s := by {
  sorry
}

example : s ∪ s = s := by {
  sorry
}

example : s ∪ s ∩ t = s := by {
  sorry
}

variable {I : Type*}
variable (A B : I → Set α)

#check mem_iUnion
#check mem_iInter

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by {
  sorry
}

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by {
  sorry
}

end

section
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by {
  sorry
}

example : f '' (s ∪ t) = f '' s ∪ f '' t := by {
  sorry
}

example : s ⊆ f ⁻¹' (f '' s) := by {
  sorry
}

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by {
  sorry
}

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by {
  sorry
}

example : f '' (f ⁻¹' u) ⊆ u := by {
  sorry
}

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by {
  sorry
}

example (h : s ⊆ t) : f '' s ⊆ f '' t := by {
  sorry
}

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by {
  sorry
}

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by {
  sorry
}

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by {
  sorry
}

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  sorry
}

example : f '' s \ f '' t ⊆ f '' (s \ t) := by {
  sorry
}

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by {
  sorry
}

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by {
  sorry
}

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by {
  sorry
}

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by {
  sorry
}

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by {
  sorry
}

end

section

open Set Real

example : InjOn log { x | x > 0 } := by
  intro x xpos y ypos
  intro e
  -- e : log x = log y
  calc
    x = exp (log x) := by rw [exp_log xpos]
    _ = exp (log y) := by rw [e]
    _ = y := by rw [exp_log ypos]


example : range exp = { y | y > 0 } := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    apply exp_pos
  intro ypos
  use log y
  rw [exp_log ypos]

example : InjOn sqrt { x | x ≥ 0 } := by {
  sorry
}

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by {
  sorry
}

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by {
  sorry
}

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by {
  sorry
}

end
