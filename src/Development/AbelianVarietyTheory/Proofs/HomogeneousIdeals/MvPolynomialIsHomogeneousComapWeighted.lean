import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsOneTmulOfForallFixed

open TensorProduct Module

namespace GlobalTheory.GaloisDescent

section Ideals

variable {K L A B G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Ring B] [Algebra K A]
  [Algebra K B] [Algebra L B] [IsScalarTower K L B] {j : A →ₐ[K] B}

theorem ideal_map_comap_of_span (I : Ideal B) (N : Submodule K A)
    (h : Submodule.span L (j.toLinearMap '' N) = I.restrictScalars L) :
    (I.comap j).map j = I := by
  refine le_antisymm Ideal.map_comap_le fun x hx => ?_
  have hle : Submodule.span L (j.toLinearMap '' N) ≤ ((I.comap j).map j).restrictScalars L := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨a, ha, rfl⟩
    refine Ideal.mem_map_of_mem j ?_
    exact h.le (Submodule.subset_span ⟨a, ha, rfl⟩)
  exact hle (h.ge hx)

theorem ideal_map_comap_of_stable (hj : IsBaseChange L j.toLinearMap) (s : G → L →+* L)
    (hs : ∀ x, (∀ g, s g x = x) → x ∈ Set.range (algebraMap K L))
    (φ : G → B →+ B) (hφ : ∀ g l a, φ g (l • j a) = s g l • j a)
    (I : Ideal B) (hI : ∀ g, ∀ x ∈ I, φ g x ∈ I) : (I.comap j).map j = I :=
  ideal_map_comap_of_span I _ (span_image_comap_eq hj s hs φ hφ (I.restrictScalars L) hI)

end Ideals

section Tensor

open Algebra.TensorProduct

variable {K L A G : Type*} [Field K] [Field L] [Algebra K L] [Ring A] [Algebra K A]

noncomputable def quotientEquivOfMapEq {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) :
    L ⊗[K] (A ⧸ I₀) ≃ₐ[L] (L ⊗[K] A) ⧸ I :=
  (tensorQuotientEquiv (R := K) L A L I₀).trans (Ideal.quotientEquivAlgOfEq L h)

@[simp]
theorem quotientEquivOfMapEq_tmul {A : Type*} [CommRing A] [Algebra K A] (I₀ : Ideal A)
    (I : Ideal (L ⊗[K] A)) (h : I₀.map (includeRight : A →ₐ[K] L ⊗[K] A) = I) (l : L) (a : A) :
    quotientEquivOfMapEq I₀ I h (l ⊗ₜ Ideal.Quotient.mk I₀ a) = Ideal.Quotient.mk I (l ⊗ₜ a) :=
  rfl

end Tensor

end GlobalTheory.GaloisDescent
