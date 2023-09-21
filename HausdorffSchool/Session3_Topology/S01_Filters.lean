import HausdorffSchool.Common
import Mathlib.Topology.Instances.Real

open Set Filter Topology

def principal {α : Type*} (s : Set α) : Filter α
    where
  sets := { t | s ⊆ t }
  univ_sets := sorry
  sets_of_superset := sorry
  inter_sets := sorry

example : Filter ℕ :=
  { sets := { s | ∃ a, ∀ b, a ≤ b → b ∈ s }
    univ_sets := sorry
    sets_of_superset := sorry
    inter_sets := sorry }

def Tendsto₁ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  ∀ V ∈ G, f ⁻¹' V ∈ F

def Tendsto₂ {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :=
  map f F ≤ G

example {X Y : Type*} (f : X → Y) (F : Filter X) (G : Filter Y) :
    Tendsto₂ f F G ↔ Tendsto₁ f F G :=
  Iff.rfl

#check (@Filter.map_mono : ∀ {α β} {m : α → β}, Monotone (map m))

#check
  (@Filter.map_map :
    ∀ {α β γ} {f : Filter α} {m : α → β} {m' : β → γ}, map m' (map m f) = map (m' ∘ m) f)

/- The above two properties allow us to prove that limits compose. -/

example {X Y Z : Type*} {F : Filter X} {G : Filter Y} {H : Filter Z} {f : X → Y} {g : Y → Z}
    (hf : Tendsto₂ f F G) (hg : Tendsto₂ g G H) : Tendsto₂ (g ∘ f) F H :=
  sorry

variable (f : ℝ → ℝ) (x₀ y₀ : ℝ)

#check comap ((↑) : ℚ → ℝ) (𝓝 x₀)

#check Tendsto (f ∘ (↑)) (comap ((↑) : ℚ → ℝ) (𝓝 x₀)) (𝓝 y₀)

section
variable {α β γ : Type*} (F : Filter α) {m : γ → β} {n : β → α}

#check (comap_comap : comap m (comap n F) = comap (n ∘ m) F)

end

example : 𝓝 (x₀, y₀) = 𝓝 x₀ ×ˢ 𝓝 y₀ :=
  nhds_prod_eq

#check le_inf_iff

/- A lot of proofs in Mathlib use all of the aforementioned structure (``map``, ``comap``, ``inf``, ``sup``, and ``prod``)
to give algebraic proofs about convergence without ever referring to members of filters.
You can practice doing this in a proof of the following lemma, unfolding the definition of ``Tendsto``
and ``Filter.prod`` if needed. -/

example (f : ℕ → ℝ × ℝ) (x₀ y₀ : ℝ) :
    Tendsto f atTop (𝓝 (x₀, y₀)) ↔
      Tendsto (Prod.fst ∘ f) atTop (𝓝 x₀) ∧ Tendsto (Prod.snd ∘ f) atTop (𝓝 y₀) :=
  sorry

/-
Consider the following statement about a sequence
``u``, a set ``M``, and a value ``x``:

  If ``u`` converges to ``x`` and ``u n`` belongs to ``M`` for
  sufficiently large ``n`` then ``x`` is in the closure of ``M``.

This can be formalized as follows:

  ``Tendsto u atTop (𝓝 x) → (∀ᶠ n in atTop, u n ∈ M) → x ∈ closure M``.

This is a special case of the theorem ``mem_closure_of_tendsto`` from the
topology library.
See if you can prove it using the quoted lemmas,
using the fact that ``ClusterPt x F`` means ``(𝓝 x ⊓ F).NeBot`` and that,
by definition, the assumption ``∀ᶠ n in atTop, u n ∈ M`` means  ``M ∈ map u atTop``. -/

#check mem_closure_iff_clusterPt
#check le_principal_iff
#check neBot_of_le

example (u : ℕ → ℝ) (M : Set ℝ) (x : ℝ) (hux : Tendsto u atTop (𝓝 x))
    (huM : ∀ᶠ n in atTop, u n ∈ M) : x ∈ closure M :=
  sorry
