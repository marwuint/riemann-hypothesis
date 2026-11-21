import Mathlib
import GroundTheory.AutomorphicForms.HermitianDisc
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Objects

namespace GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane

open NumberField GroundTheory.Automorphic Module Matrix MeasureTheory GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

section General

variable {F E W : Type*} [Field F] [Field E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [AddCommGroup W] [Module E W]

theorem lineIndex_smul {h : HermitianForm F E W} {La : AddSubgroup W} {γ : h.unitaryGroup}
    (hγ : γ • La = La) (x : W) : lineIndex E La (γ • x) = lineIndex E La x := by
  let f : W →+ W := ((γ : W ≃ₗ[E] W) : W →ₗ[E] W).toAddMonoidHom
  have hf : Function.Injective f := (γ : W ≃ₗ[E] W).injective
  have hfx : ∀ y : W, f y = γ • y := fun y => rfl
  have h1 : (ringMultiples E x).map f = ringMultiples E (γ • x) := by
    rw [ringMultiples, ringMultiples, ← AddMonoidHom.range_comp]
    congr 1
    ext a
    simp only [AddMonoidHom.comp_apply, hfx]
    simp [Subgroup.smul_def, LinearEquiv.smul_def]
  have h2 : La.map f = La := by
    conv_rhs => rw [← hγ]
    change La.map f = (γ : W ≃ₗ[E] W) • La
    rw [AddSubgroup.pointwise_smul_def]
    rfl
  have h3 : ((Submodule.span E {x}).toAddSubgroup).map f =
      (Submodule.span E {γ • x}).toAddSubgroup := by
    ext y
    simp only [AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, Submodule.mem_span_singleton]
    constructor
    · rintro ⟨z, ⟨c, rfl⟩, rfl⟩
      exact ⟨c, by rw [hfx, smul_comm]⟩
    · rintro ⟨c, rfl⟩
      exact ⟨c • x, ⟨c, rfl⟩, by rw [hfx, smul_comm]⟩
  unfold lineIndex
  conv_rhs => rw [← AddSubgroup.relIndex_map_map_of_injective _ _ hf]
  rw [AddSubgroup.map_inf_eq _ _ f hf, h1, h2, h3]

end General

abbrev Eg : Type := CyclotomicField 4 ℚ

instance : IsCyclotomicExtension {4} ℚ Eg := CyclotomicField.isCyclotomicExtension 4 ℚ

theorem finrank_Eg : finrank ℚ Eg = 2 := by
  rw [IsCyclotomicExtension.finrank (n := 4) Eg
    (Polynomial.cyclotomic.irreducible_rat (n := 4) (by norm_num))]
  decide

instance : Algebra.IsQuadraticExtension ℚ Eg := { finrank_eq_two' := finrank_Eg }

instance : IsTotallyComplex Eg := IsCyclotomicExtension.Rat.isTotallyComplex (n := 4) Eg (by norm_num)

theorem card_infinitePlace : Fintype.card (InfinitePlace Eg) = 1 := by
  have h1 := InfinitePlace.card_add_two_mul_card_eq_rank Eg
  rw [IsTotallyComplex.nrRealPlaces_eq_zero, finrank_Eg] at h1
  rw [InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces, IsTotallyComplex.nrRealPlaces_eq_zero]
  omega

instance : Subsingleton (InfinitePlace Eg) :=
  Fintype.card_le_one_iff_subsingleton.mp card_infinitePlace.le

def signs : Fin 2 → ℚˣ := ![1, -1]

def hG : HermitianForm ℚ Eg (Fin 2 → Eg) := diagForm signs

def vG : Basis (Fin 2) Eg (Fin 2 → Eg) := Pi.basisFun Eg (Fin 2)

theorem hG_apply (x y : Fin 2 → Eg) : hG.toSesq x y = conj ℚ Eg (x 0) * y 0 - conj ℚ Eg (x 1) * y 1 := by
  simp only [hG, diagForm, signs, LinearMap.mk₂'ₛₗ_apply, Fin.sum_univ_two]
  simp
  ring

def v0 : Fin 2 → Eg := fun _ => 1

def muG : Measure (archUnitary hG vG) := Measure.haar

instance : muG.IsHaarMeasure := by
  unfold muG
  infer_instance

end

end GroundTheory.Heights₂.Heights.FiniteCovolume.GaussianPlane
