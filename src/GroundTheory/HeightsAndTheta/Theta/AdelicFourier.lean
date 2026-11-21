import Mathlib
import GroundTheory.HeightsAndTheta.Theta.AdelicFourierCoord
import GroundTheory.GlobalFields.TateThesis.GaussianSchwartz
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Measure Matrix Module TensorProduct
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical nonZeroDivisors

noncomputable section

set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K]
variable {X : Type*} [AddCommGroup X] [Module K X] [FiniteDimensional K X]

variable (K X) in

abbrev AdelicPoints : Type _ := 𝔸[K] ⊗[K] X

instance : TopologicalSpace (AdelicPoints K X) := moduleTopology 𝔸[K] (AdelicPoints K X)

instance : IsModuleTopology 𝔸[K] (AdelicPoints K X) := ⟨rfl⟩

instance : ContinuousAdd (AdelicPoints K X) := IsModuleTopology.toContinuousAdd 𝔸[K] _

instance : IsTopologicalAddGroup (AdelicPoints K X) := IsModuleTopology.topologicalAddGroup 𝔸[K] _

instance : MeasurableSpace (AdelicPoints K X) := borel _

instance : BorelSpace (AdelicPoints K X) := ⟨rfl⟩

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {κ : Type*} [Fintype κ] [DecidableEq κ]

def adelicCoord (b : Basis ι K X) : AdelicPoints K X ≃ₗ[𝔸[K]] (ι → 𝔸[K]) :=
  (b.baseChange 𝔸[K]).equivFun

def adelicCoordHomeomorph (b : Basis ι K X) : AdelicPoints K X ≃ₜ (ι → 𝔸[K]) where
  toEquiv := (adelicCoord b).toEquiv
  continuous_toFun := IsModuleTopology.continuous_of_linearMap (adelicCoord b).toLinearMap
  continuous_invFun := IsModuleTopology.continuous_of_linearMap (adelicCoord b).symm.toLinearMap

variable (K X) in

def adelicPointsMeasure : Measure (AdelicPoints K X) :=
  (adeleMeasurePi K (ι := Fin (finrank K X))).map (adelicCoord (Module.finBasis K X)).symm

instance : (adelicPointsMeasure K X).IsAddHaarMeasure :=
  isAddHaarMeasure_map _ (adelicCoord (Module.finBasis K X)).symm.toLinearMap.toAddMonoidHom
    (adelicCoordHomeomorph (Module.finBasis K X)).symm.continuous
    (adelicCoord (Module.finBasis K X)).symm.surjective
    (adelicCoordHomeomorph (Module.finBasis K X)).symm.isClosedEmbedding.tendsto_cocompact

variable (B : LinearMap.BilinForm K X)

end

end GroundTheory.Heights₂.Theta
