import HausdorffSchool.Common

/-! # Practice session: Logic

First: to get these files, go to your HausdorffSchoolLean folder
in a terminal and type `git pull`.
Or, if there's an error from having edited any of the files, do
1. `git stash`
2. `git pull`
3. `git stash pop`

-/

section
/-! ## Logical connectives, some examples -/

/-! ### Implications

\to ~~> →

When in goal: `intro`/`intros`
When in hypothesis: `have` or `specialize`
-/

example (p : Prop) : p → p := by {
  intro hp
  exact hp
}

example (p q : Prop) : p → (q → p) := by {
  intro hp
  intro hq
  exact hp
}

example (p q r : Prop) : (p → q) → ((p → (q → r)) → (p → r)) := by {
  intro hpq
  intro hpqr
  intro hp
  have hq := hpq hp
  have hqr := hpqr hp
  have hr := hqr hq
  exact hr
}

/-! ### Universal quantification

\forall ~~> ∀

Same tactics as implications.
-/

example (α : Type) (p q : α → Prop) (h : ∀ x, p x → q x) :
    (∀ x, p x) → ∀ x', q x' := by {
  intro hp
  intro x'
  have := hp x'
  have := h x' this
  exact this
}

/-! ### Existential quantifier

\exists ~~> ∃

When in goal: `use`
When in hypothesis: `obtain`
-/

example : ∃ n : ℕ, n < n + 1 := by {
  use 37
  norm_num
}

example : ∃ n : ℕ, n = n := by {
  use 37
  -- `use` automatically tries applying `rfl` and a few other tactics
}

example (f : ℕ → ℕ)
    (hf : ∀ m, ∃ n, m ≤ f n) :
    ∀ m, ∃ n, m ≤ 2 * f n := by {
  intro m
  specialize hf m
  obtain ⟨n, hmf⟩ := hf
  use n
  linarith
}

/-! ### Conjunctions

\and ~~> ∧

When in goal: `constructor` (or `use`)
When in hypothesis: `obtain`

If `h : p ∧ q` then `h.1 : p` and `h.2 : q`
-/
example (p q : Prop) : p → q → p ∧ q := by {
  intro hp hq
  constructor
  · assumption
  · assumption
}

example (p q : Prop) : p ∧ q → q ∧ p := by {
  intro hpq
  obtain ⟨hp, hq⟩ := hpq
  use hq, hp
}

/-! ### Disjunctions

\or ~~> ∨

When in goal: `left`/`right`
When in hypothesis: `obtain`
-/

example (p q : Prop) : p → p ∨ q := by {
  intro hp
  left
  assumption
}

example (p q : Prop) : p ∨ q → q ∨ p := by {
  intro hpq
  obtain hp | hq := hpq
  · right
    exact hp
  · left
    exact hq
}

/-! ### Iffs

\iff ~~> ↔

When in goal: `constructor`/`use`
When in hypothesis: `rw`/`simp`/etc.

If `h : p ↔ q` then `h.mp : p → q` and `h.mpr : q → p`
-/

example (p q : Prop) : (p ↔ q) ↔ (p → q) ∧ (q → p) := by {
  constructor
  · intro hpq
    constructor
    · exact hpq.mp
    · exact hpq.mpr
  · rintro ⟨hpq, hqp⟩
    constructor
    · assumption
    · assumption
}

/-! ### Negation

\not ~~> ¬

When in goal: `intro`
When in hypothesis: `apply` (if goal is `False`), `have`

`contrapose!` and `push_neg` are useful for manipulating negations too.
-/

example (p : Prop) : ¬ p ↔ (p → False) := Iff.rfl

example (p q : Prop) (h : p → q) : ¬ q → ¬ p := by {
  intro hnq
  intro hp
  specialize h hp
  specialize hnq h
  exact hnq
}

example (p q : Prop) (hp : p) (hpq : ¬ p) : q := by {
  exact absurd hp hpq
  -- or contradiction
  -- or exact (hpq hp).elim
}

example (p : Prop) (hp : ¬ ¬ p) : p := by {
  push_neg at hp
  exact hp
}

example (p q : Prop) (h : ¬ p → ¬ q) : q → p := by {
  contrapose!
  exact h
}

/-! ## Exercises

For the remainder of this session, we will do the exercises in
HausdorffSchool/Session2_Sets_Fns_Logic/Exercises1.lean
-/
