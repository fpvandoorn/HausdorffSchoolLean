import HausdorffSchool.Common
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.MeanValue

/-! # Calculus

Reminder: to get these files, go to your HausdorffSchoolLean folder
in a terminal and type `git pull`.
-/

open Set Filter
open Topology Filter Classical Real

noncomputable section

/-! ## Elementary differential calculus -/

/-!
Derivatives are defined using Fréchet derivatives

`HasDerivAt f v x` in the case `f : ℝ → ℝ` with `x v : ℝ` means
```
(fun x' => f x' - f x - (x' - x) * v) =o[𝓝 x] fun x' => x' - x
```
-/

example : HasDerivAt sin 1 0 := by
  convert hasDerivAt_sin 0
  simp

-- The existence of a derivative without specifying its value:
example (x : ℝ) : DifferentiableAt ℝ sin x := by
  exact (hasDerivAt_sin x).differentiableAt

/-!
Every function `f : ℝ → ℝ`, no matter its differentiability, has a function
`deriv f : ℝ → ℝ` that is defined to be
1. `derive f x = v` if `HasDerivAt f v x`
2. `derive f x = 0` if `¬ DifferentiableAt ℝ f x`
Such a function is unique.

This "junk value" approach is more convenient than one where `deriv f`
requires a proof of differentiability.
-/

example {f : ℝ → ℝ} {x v : ℝ} (h : HasDerivAt f v x) :    
    deriv f x = v :=
  h.deriv

example {f : ℝ → ℝ} {x : ℝ} (h : ¬DifferentiableAt ℝ f x) : deriv f x = 0 :=
  deriv_zero_of_not_differentiableAt h

-- Lemmas take proofs of differentiability where needed
example {f g : ℝ → ℝ} {x : ℝ} (hf : DifferentiableAt ℝ f x) (hg : DifferentiableAt ℝ g x) :
    deriv (f + g) x = deriv f x + deriv g x :=
  deriv_add hf hg

-- And they don't when they don't!
example {f : ℝ → ℝ} {a : ℝ} (h : IsLocalMin f a) : deriv f a = 0 :=
  h.deriv_eq_zero

-- Rolle's theorem is true for merely continuous functions:
example {f : ℝ → ℝ} {a b : ℝ} (hab : a < b) (hfc : ContinuousOn f (Icc a b)) (hfI : f a = f b) :
    ∃ c ∈ Ioo a b, deriv f c = 0 :=
  exists_deriv_eq_zero hab hfc hfI

-- `simp` is aware of some derivatives:

example : deriv (fun x : ℝ ↦ x ^ 5) 6 = 5 * 6 ^ 4 := by simp

example : deriv (fun x : ℝ ↦ x ^ 5) = fun x => 5 * x ^ 4 := by simp

example : deriv sin π = -1 := by simp

/-! ## Normed spaces -/

section
variable {E : Type*} [NormedAddCommGroup E]

example (x : E) : 0 ≤ ‖x‖ :=
  norm_nonneg x

example {x : E} : ‖x‖ = 0 ↔ x = 0 :=
  norm_eq_zero

example (x y : E) : ‖x + y‖ ≤ ‖x‖ + ‖y‖ :=
  norm_add_le x y

#synth MetricSpace E
#synth TopologicalSpace E

variable [NormedSpace ℝ E]
#where

example (a : ℝ) (x : E) : ‖a • x‖ = |a| * ‖x‖ :=
  norm_smul a x

/-!
Derivatives are defined for functions on *nontrivially normed fields*:
-/

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (x y : 𝕜) :
    ‖x * y‖ = ‖x‖ * ‖y‖ :=
  norm_mul x y

example (𝕜 : Type*) [NontriviallyNormedField 𝕜] :
    ∃ x : 𝕜, 1 < ‖x‖ :=
  NormedField.exists_one_lt_norm 𝕜

/-- Finite-dimenionsional vector spaces over complete nontrivially normed
fields are complete. -/
example (𝕜 : Type*) [NontriviallyNormedField 𝕜] (E : Type*) [NormedAddCommGroup E]
    [NormedSpace 𝕜 E] [CompleteSpace 𝕜] [FiniteDimensional 𝕜 E] : CompleteSpace E :=
  FiniteDimensional.complete 𝕜 E

end

/-! # Continuous linear maps -/
section

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]

example : E →L[𝕜] E :=
  ContinuousLinearMap.id 𝕜 E

example (f : E →L[𝕜] F) : E → F :=
  f

example (f : E →L[𝕜] F) : Continuous f :=
  f.cont

example (f : E →L[𝕜] F) (x y : E) : f (x + y) = f x + f y :=
  f.map_add x y

example (f : E →L[𝕜] F) (a : 𝕜) (x : E) : f (a • x) = a • f x :=
  f.map_smul a x

-- Operator norm:

variable (f : E →L[𝕜] F)

example (x : E) : ‖f x‖ ≤ ‖f‖ * ‖x‖ :=
  f.le_op_norm x

example {M : ℝ} (hMp : 0 ≤ M) (hM : ∀ x, ‖f x‖ ≤ M * ‖x‖) : ‖f‖ ≤ M :=
  f.op_norm_le_bound hMp hM

end

/-! ## Asymptotic comparisons -/

section
variable {α : Type*} {E : Type*} [NormedGroup E] {F : Type*} [NormedGroup F]
    (l : Filter α) (f : α → E) (g : α → F)
open Asymptotics

example (c : ℝ) : IsBigOWith c l f g ↔ ∀ᶠ x in l, ‖f x‖ ≤ c * ‖g x‖ :=
  isBigOWith_iff

example : f =O[l] g ↔ ∃ C, IsBigOWith C l f g :=
  isBigO_iff_isBigOWith

example : f =o[l] g ↔ ∀ C > 0, IsBigOWith C l f g :=
  isLittleO_iff_forall_isBigOWith

example {E : Type*} [NormedAddCommGroup E] (f g : α → E) :
    f ~[l] g ↔ (f - g) =o[l] g :=
  Iff.rfl

end

/-! ## Differentiability -/

section
variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
  {F : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F]
open Topology

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) :
    HasFDerivAt f f' x₀ ↔
      (fun x ↦ f x - f x₀ - f' (x - x₀)) =o[𝓝 x₀] (fun x ↦ x - x₀) :=
  Iff.rfl

example (f : E → F) (f' : E →L[𝕜] F) (x₀ : E) (hff' : HasFDerivAt f f' x₀) :
    fderiv 𝕜 f x₀ = f' :=
  hff'.fderiv

end