import HausdorffSchool.Common
import Mathlib.Data.Set.Basic

/-! # Practice session: Sets and functions

-/

namespace MyDefs

/-- A set of elements of `α` is a predicate with domain `α`.

If we regard `α` as iteslf being a set, then `Set α`
is the power set of `α`. -/
def Set (α : Type*) := (α → Prop)

variable {α : Type*}

/-- Given a predicate, make its type be `Set α`,
thereby making it "be" a set. -/
def setOf (p : α → Prop) : Set α := p

/-- Set membership predicate. -/
def Set.mem (x : α) (s : Set α) : Prop := s x

/-- Enable `∈` notation. -/
instance : Membership α (Set α) where mem := Set.mem

example (x : α) (s : Set α) : x ∈ s ↔ s x := Iff.rfl

-- Error. The notation wants to see `Set α` to work.
--example (x : α) (s : α → Prop) : x ∈ s ↔ s x := Iff.rfl

lemma Set.ext (s t : Set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by {
  constructor
  · intro h x
    rw [h]
  · intro h
    funext x
    apply propext
    exact h x
}

lemma Set.ext' (s t : Set α) : s = t ↔ ∀ x, x ∈ s ↔ x ∈ t := by {
  conv =>
    rhs
    ext
    rw [← eq_iff_iff]
  exact Function.funext_iff
}

notation "my{" x " | " p "}" => setOf fun x => p

#check my{(n : Nat) | 0 < n}

/-- s ∪ t -/
def Set.union (s t : Set α) : Set α := my{x | x ∈ s ∨ x ∈ t}
/-- s ∩ t -/
def Set.inter (s t : Set α) : Set α := my{x | x ∈ s ∧ x ∈ t}
/-- s \ t -/
def Set.diff (s t : Set α) : Set α := my{x | x ∈ s ∧ ¬ x ∈ t}
/-- sᶜ -/
def Set.compl (s : Set α) : Set α := my{x | ¬ x ∈ s}
/-- s ⊆ t -/
def Set.IsSubset (s t : Set α) : Prop := ∀ x, x ∈ s → x ∈ t
/-- ∅ -/
def Set.empty : Set α := my{x | False}
def Set.univ : Set α := my{x | True}

lemma Set.mem_setOf (p : α → Prop) (x : α) : x ∈ my{x' | p x'} ↔ p x := Iff.rfl

lemma Set.mem_union (s t : Set α) (x : α) :
    x ∈ Set.union s t ↔ x ∈ s ∨ x ∈ t := Iff.rfl

lemma Set.mem_inter_iff (s t : Set α) (x : α) :
    x ∈ Set.inter s t ↔ x ∈ s ∧ x ∈ t := Iff.rfl

#check Set.mem_diff
#check Set.mem_compl_iff
#check Set.subset_def

end MyDefs

open Set

variable {α β : Type*} (s t u : Set α)

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  rw [subset_def]
  rw [subset_def] at h
  intro x
  rw [mem_inter_iff, mem_inter_iff]
  intro h'
  specialize h x
  specialize h h'.1
  constructor
  · exact h
  · exact h'.2

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  intro x
  rintro ⟨hs, ht⟩
  exact ⟨h hs, ht⟩

example (h : s ⊆ t) : s ∩ u ⊆ t ∩ u := by
  exact inter_subset_inter_left u h

example : s ∪ t = t ∪ s := by {
  ext x
  rw [mem_union, mem_union, or_comm]
}

/-! ## Functions -/

variable (f : α → β)

#check Set.preimage
example (s : Set β) : f ⁻¹' s = {x | f x ∈ s} := rfl

#check Set.image
example (s : Set α) : f '' s = {y | ∃ x, x ∈ s ∧ f x = y} := rfl

#check Set.mem_preimage
-- Can do `rw [Set.preimage]`

#check Set.mem_image
-- Can do `rw [Set.image]`

/-! ## Exercises

For the remainder of this session, we will do the exercises in
HausdorffSchool/Session2_Sets_Fns_Logic/Exercises2.lean
-/
