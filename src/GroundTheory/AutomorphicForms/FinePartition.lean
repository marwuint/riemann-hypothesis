import Mathlib

namespace GroundTheory.Automorphic

open Set Filter Topology Uniformity UniformSpace Function

structure MeasurablePartition (X : Type*) [MeasurableSpace X] where

  n : ℕ

  E : ℕ → Set X
  measurableSet : ∀ i, MeasurableSet (E i)
  disjoint : Pairwise (Disjoint on E)
  exists_mem : ∀ x, ∃ i < n, x ∈ E i

namespace MeasurablePartition

variable {X : Type*} [MeasurableSpace X]

instance : Inhabited (MeasurablePartition X) where
  default :=
    { n := 1
      E := fun i => if i = 0 then univ else ∅
      measurableSet := fun i => by split_ifs <;> simp
      disjoint := by
        intro i j hij
        simp only [Function.onFun]
        by_cases hi : i = 0
        · have hj : j ≠ 0 := fun h => hij (hi.trans h.symm)
          simp [hj]
        · simp [hi]
      exists_mem := fun x => ⟨0, Nat.one_pos, by simp⟩ }

variable (p : MeasurablePartition X)

open Classical in

noncomputable def index (x : X) : ℕ := Nat.find (p.exists_mem x)

def IsFine (V : SetRel X X) : Prop := ∀ i, ∀ x ∈ p.E i, ∀ y ∈ p.E i, (x, y) ∈ V

end MeasurablePartition

open MeasurablePartition

section Filter

variable (X : Type*) [UniformSpace X]

def fineFilter : Filter (SetRel X X) := (𝓤 X).smallSets ⊓ 𝓟 {V | V ∈ 𝓤 X}

instance : (fineFilter X).NeBot := by
  refine Filter.inf_principal_neBot_iff.2 fun U hU => ?_
  obtain ⟨t, ht, htU⟩ := (hasBasis_smallSets _).mem_iff.1 hU
  exact ⟨t, htU (mem_powerset subset_rfl), ht⟩

variable {X}

variable [MeasurableSpace X] [CompactSpace X] [OpensMeasurableSpace X]

end Filter

section Measurable

variable {X Y : Type*} [UniformSpace X] [CompactSpace X] [MeasurableSpace X]
  [OpensMeasurableSpace X] [UniformSpace Y] [CompactSpace Y] [MeasurableSpace Y]
  [OpensMeasurableSpace Y]

end Measurable

end GroundTheory.Automorphic
