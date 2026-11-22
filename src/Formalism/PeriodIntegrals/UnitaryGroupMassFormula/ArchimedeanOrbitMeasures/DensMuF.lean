import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.DensMuP

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct RealInnerProductSpace FourierTransform
open MeasureTheory NumberField Topology Set Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets
  Formalism.L2.SG.Sub Matrix

def BetaSym : Prop := ∀ {D : D7} (X : HidaSetting D) (x y : EuclideanSpace ℝ (KapI X)), betaI X x y = betaI X y x

section
variable {D : D7} (X : HidaSetting D)

open Classical in

def Alin : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] EuclideanSpace ℝ (KapI X) :=
  ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm : (KapI X → ℝ) →ₗ[ℝ] EuclideanSpace ℝ (KapI X)) ∘ₗ
    Matrix.toLin' (matI X) ∘ₗ
    ((EuclideanSpace.equiv (KapI X) ℝ).toLinearEquiv.symm.symm : EuclideanSpace ℝ (KapI X) →ₗ[ℝ] (KapI X → ℝ))

open Classical in
theorem det_Alin : LinearMap.det (Alin X) = (matI X).det := by
  rw [Alin, LinearMap.det_conj, LinearMap.det_toLin']

theorem inner_Alin (x y : EuclideanSpace ℝ (KapI X)) : ⟪x, Alin X y⟫ = betaI X x y := by
  classical
  rw [betaI_expand]
  simp only [Alin, PiLp.inner_apply, LinearMap.coe_comp, Function.comp_apply, Matrix.toLin'_apply,
    LinearEquiv.coe_coe]
  simp
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.mulVec, dotProduct]
  have hy : ∀ j, (EuclideanSpace.equiv (KapI X) ℝ) y j = y j := fun j => rfl
  simp only [hy]
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

end

end PI.AprimeInfW
