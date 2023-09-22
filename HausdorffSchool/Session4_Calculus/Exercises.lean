import HausdorffSchool.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

open Set Filter
open Topology Filter Classical Real

noncomputable

example (x : ℝ) :
    deriv (fun x : ℝ ↦ x ^ 5 + x ^ 2 + 1) x = 5 * x ^ 4 + 2 * x := by {
  sorry
}

example (x : ℝ) : 
    deriv (fun x : ℝ ↦ (x + 1) * (x + 2)) x = 2 * x + 3 := by {
  sorry
}

/-- This theorem appears to be missing from mathlib.
Away from zero there is `DifferentiableAt.norm`.
You do not need to prove it, but if you do maybe you could contribute it
if it really doesn't exist! -/
theorem not_differentiableAt_abs :
    ¬ DifferentiableAt ℝ (fun x : ℝ ↦ abs x) 0 := by {
  sorry
}

example :
    deriv (fun x : ℝ ↦ |x|) 0 = 0 := by {
  sorry
}

example
    (bad : ∀ (f g : ℝ → ℝ) (x : ℝ), deriv (f + g) x = deriv f x + deriv g x) :
    False := by {
  sorry
}

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

example (x : E) (hx : x ≠ 0) (c : ℝ) : ‖c • x‖ = 0 ↔ c = 0 := by {
  sorry
}

example (x y : E) : ‖x‖ - ‖y‖ ≤ ‖x - y‖ := by {
  sorry
}

example (x y : E) (c d : ℝ) :
    ‖c • x + d • y‖ ≤ |c| • ‖x‖ + |d| • ‖y‖ := by {
  sorry
}

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

example (f : E →L[ℝ] F) (x y : E) (c d : ℝ) : f (c • x + d • y) = c • f x + d • f y := by {
  sorry
}

end

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E : Type*} [NormedAddCommGroup E]
  [NormedSpace 𝕜 E] {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

open Metric

/-
As a challenging exercise, you could try to prove the Banach-Steinhaus theorem,
also known as the Uniform Boundedness Principle.
The principle states that a family of continuous linear maps from a Banach space
into a normed space is pointwise bounded, then the norms of these linear maps are uniformly bounded.
The main ingredient is Baire’s theorem `nonempty_interior_of_iUnion_of_closed`.
Minor ingredients include `continuous_linear_map.op_norm_le_of_shell`, `interior_subset`
and `interior_iInter_subset` and `is_closed_le`.
-/
example {ι : Type*} [CompleteSpace E] {g : ι → E →L[𝕜] F} (h : ∀ x, ∃ C, ∀ i, ‖g i x‖ ≤ C) :
    ∃ C', ∀ i, ‖g i‖ ≤ C' := by
  -- sequence of subsets consisting of those `x : E` with norms `‖g i x‖` bounded by `n`
  let e : ℕ → Set E := fun n ↦ ⋂ i : ι, { x : E | ‖g i x‖ ≤ n }
  -- each of these sets is closed
  have hc : ∀ n : ℕ, IsClosed (e n)
  sorry
  -- the union is the entire space; this is where we use `h`
  have hU : (⋃ n : ℕ, e n) = univ
  sorry
  /- apply the Baire category theorem to conclude that for some `m : ℕ`,
       `e m` contains some `x` -/
  obtain ⟨m, x, hx⟩ : ∃ m, ∃ x, x ∈ interior (e m) := sorry
  obtain ⟨ε, ε_pos, hε⟩ : ∃ ε > 0, ball x ε ⊆ interior (e m) := sorry
  obtain ⟨k, hk⟩ : ∃ k : 𝕜, 1 < ‖k‖ := sorry
  -- show all elements in the ball have norm bounded by `m` after applying any `g i`
  have real_norm_le : ∀ z ∈ ball x ε, ∀ (i : ι), ‖g i z‖ ≤ m
  sorry
  have εk_pos : 0 < ε / ‖k‖ := sorry
  refine' ⟨(m + m : ℕ) / (ε / ‖k‖), fun i ↦ ContinuousLinearMap.op_norm_le_of_shell ε_pos _ hk _⟩
  sorry
  sorry

end