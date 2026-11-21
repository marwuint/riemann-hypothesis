import Mathlib

open scoped BigOperators
open Module

namespace GlobalTheory

section Frames

variable {ι : Type*} {K : Type*} {V : ι → Type*}

section Semiring

variable [CommSemiring K] [∀ s, AddCommMonoid (V s)] [∀ s, Module K (V s)]
  {l m n : ι → Type*} [∀ s, Fintype (l s)] [∀ s, Fintype (m s)]

abbrev EntryIndex (m n : ι → Type*) : Type _ := Σ s, m s × n s

def entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) : EntryIndex m n → α :=
  fun k => b k.1 k.2.1 k.2.2

def ofEntries {α : Type*} (ξ : EntryIndex m n → α) : ∀ s, Matrix (m s) (n s) α :=
  fun s => Matrix.of fun i j => ξ ⟨s, i, j⟩

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_apply {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) (s : ι) (i : m s)
    (j : n s) : entries b ⟨s, i, j⟩ = b s i j := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_apply {α : Type*} (ξ : EntryIndex m n → α) (s : ι) (i : m s)
    (j : n s) : ofEntries ξ s i j = ξ ⟨s, i, j⟩ := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem entries_ofEntries {α : Type*} (ξ : EntryIndex m n → α) :
    entries (ofEntries ξ) = ξ := rfl

omit [∀ s, Fintype (m s)] in
@[simp] theorem ofEntries_entries {α : Type*} (b : ∀ s, Matrix (m s) (n s) α) :
    ofEntries (entries b) = b := rfl

end Semiring

variable [Fintype ι] {r : ι → ℕ} [Field K] [∀ s, AddCommGroup (V s)] [∀ s, Module K (V s)]
  {W : Type*} [AddCommGroup W] [Module K W]

end Frames

end GlobalTheory
