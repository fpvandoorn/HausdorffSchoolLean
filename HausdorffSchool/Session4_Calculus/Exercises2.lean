import HausdorffSchool.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff
import Mathlib.Analysis.Calculus.IteratedDeriv

noncomputable section

open Real Filter Classical

/-!
# Derivatives

Lean can automatically compute some simple derivatives using `simp` tactic.
-/

example : deriv (fun x : ℝ ↦ x^5) 6 = 5 * 6^4 := by sorry

example (x₀ : ℝ) (h₀ : x₀ ≠ 0) :
    deriv (fun x : ℝ ↦ 1 / x) x₀ = -1 / x₀^2 := by sorry

example : deriv sin π = -1 := by sorry

-- Sometimes you need `ring` and/or `field_simp` after `simp`
example (x₀ : ℝ) (h : x₀ ≠ 0) :
  deriv (fun x : ℝ ↦ Real.exp (x^2) / x^5) x₀ = (2 * x₀^2 - 5) * exp (x₀^2) / x₀^6 := by
  have : x₀^5 ≠ 0
  · sorry
  simp [this]
  sorry

example (a b x₀ : ℝ) (h : x₀ ≠ 1) :
    deriv (fun x ↦ (a * x + b) / (x - 1)) x₀ = -(a + b) / (x₀ - 1)^2 := by
  sorry

-- Currently `simp` is unable to solve the next example.
-- A PR that will make this example provable `by simp` would be very welcome!
example : iteratedDeriv 7 (fun x ↦ sin (tan x) - tan (sin x)) 0 = -168 := sorry

variable (m n : Type) [Fintype m] [Fintype n]

-- We tell Lean that Matrices form a normed space
instance : NormedAddCommGroup (Matrix m n ℝ) := Pi.normedAddCommGroup
instance : NormedSpace ℝ (Matrix m n ℝ) := Pi.normedSpace

/-- Trace of a matrix as a continuous linear map. -/
def Matrix.traceCLM : Matrix n n ℝ →L[ℝ] ℝ := by
  apply (Matrix.traceLinearMap n ℝ ℝ).mkContinuous (Fintype.card n)
  sorry

-- Another hard exercise that would make a very good PR
example :
    HasFDerivAt (λ m : Matrix n n ℝ ↦ m.det) (Matrix.traceCLM n) 1 := by
  sorry


open Set TopologicalSpace
