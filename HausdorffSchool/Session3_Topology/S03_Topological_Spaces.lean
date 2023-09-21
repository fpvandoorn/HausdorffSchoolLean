import HausdorffSchool.Common
import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.NormedSpace.BanachSteinhaus

open Set Filter Topology

section
variable {X : Type*} [TopologicalSpace X]
variable {Y : Type*} [TopologicalSpace Y]

#check TopologicalSpace.mkOfNhds
#check TopologicalSpace.nhds_mkOfNhds

example {α : Type*} (n : α → Filter α) (H₀ : ∀ a, pure a ≤ n a)
    (H : ∀ a : α, ∀ p : α → Prop, (∀ᶠ x in n a, p x) → ∀ᶠ y in n a, ∀ᶠ x in n y, p x) :
    ∀ a, ∀ s ∈ n a, ∃ t ∈ n a, t ⊆ s ∧ ∀ a' ∈ t, s ∈ n a' :=
  sorry

end

variable {X Y : Type*}

/- Our main goal is now to prove the basic theorem which allows extension by continuity.
From Bourbaki's general topology book, I.8.5, Theorem 1 (taking only the non-trivial implication):

Let `X` be a topological space, `A` a dense subset of `X`, `f : A → Y`
a continuous mapping of `A` into a regular space `Y`. If, for each `x` in `X`,
`f(y)` tends to a limit in `Y` when `y` tends to `x`
while remaining in `A` then there exists a continuous extension `φ` of `f` to
`X`.

Actually Mathlib contains a more general version of the above lemma, ``DenseInducing.continuousAt_extend``,
but we'll stick to Bourbaki's version here.

Remember that, given ``A : Set X``, ``↥A`` is the subtype associated to ``A``, and Lean will automatically
insert that funny up arrow when needed. And the (inclusion) coercion map is ``(↑) : A → X``.
The assumption "tends to `x` while remaining in `A`" corresponds to the pull-back filter
``comap (↑) (𝓝 x)``.

Let's prove first an auxiliary lemma, extracted to simplify the context
(in particular we don't need Y to be a topological space here). -/

theorem aux {X Y A : Type*} [TopologicalSpace X] {c : A → X}
      {f : A → Y} {x : X} {F : Filter Y}
      (h : Tendsto f (comap c (𝓝 x)) F) {V' : Set Y} (V'_in : V' ∈ F) :
    ∃ V ∈ 𝓝 x, IsOpen V ∧ c ⁻¹' V ⊆ f ⁻¹' V' :=
  sorry

/-
Let's now turn to the main proof of the extension by continuity theorem.

When Lean needs a topology on ``↥A`` it will automatically use the induced topology.
The only relevant lemma is
``nhds_induced (↑) : ∀ a : ↥A, 𝓝 a = comap (↑) (𝓝 ↑a)``
(this is actually a general lemma about induced topologies).

The proof outline is:

The main assumption and the axiom of choice give a function ``φ`` such that
``∀ x, Tendsto f (comap (↑) (𝓝 x)) (𝓝 (φ x))``
(because ``Y`` is Hausdorff, ``φ`` is entirely determined, but we won't need that until we try to
prove that ``φ`` indeed extends ``f``).

Let's first prove ``φ`` is continuous. Fix any ``x : X``.
Since ``Y`` is regular, it suffices to check that for every *closed* neighborhood
``V'`` of ``φ x``, ``φ ⁻¹' V' ∈ 𝓝 x``.
The limit assumption gives (through the auxiliary lemma above)
some ``V ∈ 𝓝 x`` such ``IsOpen V ∧ (↑) ⁻¹' V ⊆ f ⁻¹' V'``.
Since ``V ∈ 𝓝 x``, it suffices to prove ``V ⊆ φ ⁻¹' V'``, ie  ``∀ y ∈ V, φ y ∈ V'``.
Let's fix ``y`` in ``V``. Because ``V`` is *open*, it is a neighborhood of ``y``.
In particular ``(↑) ⁻¹' V ∈ comap (↑) (𝓝 y)`` and a fortiori ``f ⁻¹' V' ∈ comap (↑) (𝓝 y)``.
In addition ``comap (↑) (𝓝 y) ≠ ⊥`` because ``A`` is dense.
Because we know ``Tendsto f (comap (↑) (𝓝 y)) (𝓝 (φ y))`` this implies
``φ y ∈ closure V'`` and, since ``V'`` is closed, we have proved ``φ y ∈ V'``.

It remains to prove that ``φ`` extends ``f``. This is were continuity of ``f`` enters the discussion,
together with the fact that ``Y`` is Hausdorff. -/

example [TopologicalSpace X] [TopologicalSpace Y] [RegularSpace Y] {A : Set X}
    (hA : ∀ x, x ∈ closure A) {f : A → Y} (f_cont : Continuous f)
    (hf : ∀ x : X, ∃ c : Y, Tendsto f (comap (↑) (𝓝 x)) (𝓝 c)) :
    ∃ φ : X → Y, Continuous φ ∧ ∀ a : A, φ a = f a :=
  sorry

variable [TopologicalSpace X]

example {F : Filter X} {x : X} : ClusterPt x F ↔ NeBot (𝓝 x ⊓ F) :=
  Iff.rfl

example {s : Set X} :
    IsCompact s ↔ ∀ (F : Filter X) [NeBot F], F ≤ 𝓟 s → ∃ a ∈ s, ClusterPt a F :=
  Iff.rfl

example [TopologicalSpace.FirstCountableTopology X] {s : Set X} {u : ℕ → X} (hs : IsCompact s)
    (hu : ∀ n, u n ∈ s) : ∃ a ∈ s, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Tendsto (u ∘ φ) atTop (𝓝 a) :=
  hs.tendsto_subseq hu

variable [TopologicalSpace Y]

example {x : X} {F : Filter X} {G : Filter Y} (H : ClusterPt x F) {f : X → Y}
    (hfx : ContinuousAt f x) (hf : Tendsto f F G) : ClusterPt (f x) G :=
  ClusterPt.map H hfx hf

/-
As an exercise, we will prove that the image of a compact set under a continuous map is
compact. In addition to the above properties, you should use ``Filter.push_pull`` and
``NeBot.of_map``. -/

example [TopologicalSpace Y] {f : X → Y} (hf : Continuous f) {s : Set X} (hs : IsCompact s) :
    IsCompact (f '' s) := by
  intro F F_ne F_le
  have map_eq : map f (𝓟 s ⊓ comap f F) = 𝓟 (f '' s) ⊓ F := by sorry
  have Hne : (𝓟 s ⊓ comap f F).NeBot := by sorry
  have Hle : 𝓟 s ⊓ comap f F ≤ 𝓟 s := inf_le_left
  sorry