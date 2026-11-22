import Mathlib
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.SymbolBridgeSum
import GroundTheory.ProfiniteCohomology.GlobalClassFormation.OpenSubgroups
import GroundTheory.GlobalFields.GlobalArtinMap.Kernel
set_option maxSynthPendingDepth 1

namespace GroundTheory.Global

open NumberField IntermediateField IsDedekindDomain IdeleGroup FiniteSubfield GroundTheory.ProfCoh GroundTheory.LocalField

local notation "ℚ̄" => AlgebraicClosure ℚ

noncomputable section

section Transport

variable {K : Type*} [Field K] [NumberField K] {L L' : Type*} [Field L] [NumberField L] [Field L']
  [NumberField L'] [Algebra K L] [Algebra K L'] [IsGalois K L] [IsGalois K L']
  [IsMulCommutative (L ≃ₐ[K] L)] [IsMulCommutative (L' ≃ₐ[K] L')]

theorem ideleSymbol_apply_algEquiv (e : L ≃ₐ[K] L') (x : IdeleGroup K) (l : L) :
    ideleSymbol K L' x (e l) = e (ideleSymbol K L x l) := by
  let _ : Algebra L L' := e.toRingHom.toAlgebra
  have : IsScalarTower K L L' := IsScalarTower.of_algebraMap_eq fun a ↦ (e.commutes a).symm
  have h := AlgEquiv.restrictNormal_commutes (ideleSymbol K L' x) L l
  rw [restrictNormal_ideleSymbol L L' x] at h
  exact h.symm

end Transport

section Bridge

variable {K : FiniteSubfield} (E : FiniteSubfield) [hKE : Fact (K ≤ E)]

abbrev overField (K E : FiniteSubfield) [hKE : Fact (K ≤ E)] : IntermediateField K.1 ℚ̄ :=
  extendScalars (show K.1 ≤ E.1 from hKE.out)

def overFieldEquiv (K E : FiniteSubfield) [Fact (K ≤ E)] : E.1 ≃ₐ[K.1] ↥(overField K E) :=
  AlgEquiv.ofRingEquiv (f :=
    { toFun := fun y ↦ ⟨(y : ℚ̄), y.2⟩
      invFun := fun y ↦ ⟨(y : ℚ̄), y.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_mul' := fun _ _ ↦ rfl
      map_add' := fun _ _ ↦ rfl }) fun _ ↦ rfl

@[simp]
theorem coe_overFieldEquiv (y : E.1) : ((overFieldEquiv K E y : ↥(overField K E)) : ℚ̄) = (y : ℚ̄) :=
  rfl

variable [(E.1.fixingSubgroup.subgroupOf K.1.fixingSubgroup).Normal] [IsMulCommutative (E.1 ≃ₐ[K.1] E.1)]

attribute [local instance] FiniteSubfield.isGalois_of_normal

instance : FiniteDimensional K.1 ↥(overField K E) :=
  LinearEquiv.finiteDimensional (overFieldEquiv K E).toLinearEquiv

instance : IsGalois K.1 ↥(overField K E) := IsGalois.of_algEquiv (overFieldEquiv K E)

instance : IsMulCommutative (↥(overField K E) ≃ₐ[K.1] ↥(overField K E)) :=
  ⟨⟨fun σ τ ↦ by
    apply (AlgEquiv.autCongr (overFieldEquiv K E)).symm.injective
    simp only [map_mul]
    exact mul_comm' _ _⟩⟩

instance : IsAbelianGalois K.1 ↥(overField K E) := ⟨⟩

end Bridge

variable {K : FiniteSubfield} (ι : LocalEmbeddings K)

end

end GroundTheory.Global
