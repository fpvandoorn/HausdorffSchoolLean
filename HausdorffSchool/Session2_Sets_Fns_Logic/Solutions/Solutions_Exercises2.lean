import HausdorffSchool.Common
import Mathlib.Data.Set.Basic

open Set Function

section
variable {α β : Type*} (s t u : Set α)

example : s ∩ (t ∪ u) ⊆ s ∩ t ∪ s ∩ u := by {
  intro x
  rw [mem_inter_iff, mem_union, mem_union, mem_inter_iff]
  rintro ⟨hs, ht | hu⟩
  · left
    use hs, ht
  · right
    use hs, hu
}

example : s ∩ t ∪ s ∩ u ⊆ s ∩ (t ∪ u) := by {
  rintro x (⟨hs, ht⟩ | ⟨hs, hu⟩)
  · use hs
    left
    assumption
  · use hs
    right
    assumption
}

example : (s \ t) \ u ⊆ s \ (t ∪ u) := by {
  intro x
  simp only [mem_diff, mem_union, not_or, and_imp]
  -- Use LHS's of implications when simplifying RHS's
  simp (config := {contextual := true})
}

example : s \ (t ∪ u) ⊆ (s \ t) \ u := by {
  intro x
  simp (config := {contextual := true}) [not_or]
}

example : s ∩ t = t ∩ s := by {
  ext x
  rw [mem_inter_iff, and_comm, ← mem_inter_iff]
}

example : s ∪ s = s := by {
  ext x
  rw [mem_union, or_self]
}

example : s ∪ s ∩ t = s := by {
  ext x
  rw [mem_union, mem_inter_iff]
  constructor
  · rintro (hs | ⟨hs, _ht⟩)
    · assumption
    · assumption
  · intro hs
    simp [hs]
}

variable {I : Type*}
variable (A B : I → Set α)

#check mem_iUnion
#check mem_iInter

example : (s ∩ ⋃ i, A i) = ⋃ i, A i ∩ s := by {
  ext x
  simp_rw [mem_inter_iff, mem_iUnion, mem_inter_iff]
  rw [exists_and_right, and_comm]
}

example : (s ∪ ⋂ i, A i) = ⋂ i, A i ∪ s := by {
  ext x
  simp_rw [mem_union, mem_iInter, mem_union]
  rw [forall_or_right, or_comm]
}

end

section
variable {α β : Type*}
variable (f : α → β)
variable (s t : Set α)
variable (u v : Set β)

example : f ⁻¹' (u ∩ v) = f ⁻¹' u ∩ f ⁻¹' v := by {
  rfl
}

example : f '' (s ∪ t) = f '' s ∪ f '' t := by {
  ext x
  simp [or_and_right, exists_or]
}

example : s ⊆ f ⁻¹' (f '' s) := by {
  intro x h
  rw [mem_preimage, mem_image]
  use x
}

example : f '' s ⊆ v ↔ s ⊆ f ⁻¹' v := by {
  exact image_subset_iff -- maybe cheating...
}

example (h : Injective f) : f ⁻¹' (f '' s) ⊆ s := by {
  intro x
  rw [mem_preimage, mem_image]
  rintro ⟨x', hx, hf⟩ 
  have := h hf
  rw [← this]
  assumption
}

example : f '' (f ⁻¹' u) ⊆ u := by {
  intro x
  simp_rw [mem_image, mem_preimage]
  rintro ⟨x', hx', rfl⟩
  exact hx'
}

example (h : Surjective f) : u ⊆ f '' (f ⁻¹' u) := by {
  intro x hx
  simp_rw [mem_image, mem_preimage]
  specialize h x
  obtain ⟨y, rfl⟩ := h
  use y
}

example (h : s ⊆ t) : f '' s ⊆ f '' t := by {
  intro x
  simp_rw [mem_image]
  rintro ⟨x, hx, rfl⟩
  use x, h hx
}

example (h : u ⊆ v) : f ⁻¹' u ⊆ f ⁻¹' v := by {
  intro x
  simp_rw [mem_preimage]
  apply h
}

example : f ⁻¹' (u ∪ v) = f ⁻¹' u ∪ f ⁻¹' v := by {
  rfl
}

example : f '' (s ∩ t) ⊆ f '' s ∩ f '' t := by {
  intro x
  simp only [mem_image, mem_inter_iff, forall_exists_index, and_imp] -- from simp?
  rintro y hs ht rfl
  constructor
  · use y
  · use y  
}

example (h : Injective f) : f '' s ∩ f '' t ⊆ f '' (s ∩ t) := by {
  intro x
  simp only [mem_inter_iff, mem_image, and_imp, forall_exists_index] -- from simp?
  rintro a hs rfl a' ht hf
  use a'
  obtain rfl := h hf
  simp [*]
}

example : f '' s \ f '' t ⊆ f '' (s \ t) := by {
  intro y
  simp only [mem_diff, mem_image, not_exists, not_and, and_imp, forall_exists_index]
  rintro x hs rfl h
  use x
  simp only [hs, true_and, and_true]
  intro ht
  have := h _ ht
  exact this rfl
}

example : f ⁻¹' u \ f ⁻¹' v ⊆ f ⁻¹' (u \ v) := by {
  intro x
  simp
}

example : f '' s ∩ v = f '' (s ∩ f ⁻¹' v) := by {
  ext x
  simp only [mem_inter_iff, mem_image, mem_preimage]
  constructor
  · rintro ⟨⟨y, hy, rfl⟩, hz⟩
    use y
  · rintro ⟨y, ⟨hy, hf⟩, rfl⟩
    use! y
}

example : f '' (s ∩ f ⁻¹' u) ⊆ f '' s ∩ u := by {
  intro x
  simp only [mem_image, mem_inter_iff, mem_preimage, forall_exists_index, and_imp]
  rintro y hy hfy rfl
  use! y
}

example : s ∩ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∩ u) := by {
  rintro x ⟨hs, hf⟩
  rw [mem_preimage, mem_inter_iff, mem_image]
  refine ⟨?_, hf⟩
  use x 
}

example : s ∪ f ⁻¹' u ⊆ f ⁻¹' (f '' s ∪ u) := by {
  intro x
  simp only [mem_union, mem_preimage, preimage_union, mem_image]
  rintro (hs | hu)
  · left
    use x
  · right
    exact hu
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
  intro x xnonneg y ynonneg
  intro e
  calc
    x = sqrt x ^ 2 := by rw [sq_sqrt xnonneg]
    _ = sqrt y ^ 2 := by rw [e]
    _ = y := by rw [sq_sqrt ynonneg]
}

example : InjOn (fun x ↦ x ^ 2) { x : ℝ | x ≥ 0 } := by {
  intro x xnonneg y ynonneg
  intro e
  dsimp at *
  calc
    x = sqrt (x ^ 2) := by rw [sqrt_sq xnonneg]
    _ = sqrt (y ^ 2) := by rw [e]
    _ = y := by rw [sqrt_sq ynonneg]
}

example : sqrt '' { x | x ≥ 0 } = { y | y ≥ 0 } := by {
  ext y; constructor
  · rintro ⟨x, ⟨xnonneg, rfl⟩⟩
    apply sqrt_nonneg
  intro ynonneg
  use y ^ 2
  dsimp at *
  constructor
  apply pow_nonneg ynonneg
  apply sqrt_sq
  assumption
}

example : (range fun x ↦ x ^ 2) = { y : ℝ | y ≥ 0 } := by {
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    dsimp at *
    apply pow_two_nonneg
  intro ynonneg
  use sqrt y
  exact sq_sqrt ynonneg
}

end
