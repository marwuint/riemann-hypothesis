import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.WmSysObjects
import GroundTheory.HeightsAndTheta.Theta.SchroedingerTranslates.ExistsInverseFontaineElementMemFilNegOne
import GroundTheory.HeightsAndTheta.Theta.LocallyCompactField.Countability

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace WmSysEquiv

open MeasureTheory Measure Topology Filter Set
open scoped NNReal ENNReal Pointwise

set_option linter.unusedSectionVars false

section Pi

variable {F : Type*} [Field F] [TopologicalSpace F] [IsTopologicalRing F] [LocallyCompactSpace F]
  {ι : Type*} [Fintype ι] [DecidableEq ι]

def piHomeo (L : (ι → F) ≃ₗ[F] (ι → F)) : (ι → F) ≃ₜ+ (ι → F) :=
  { L.toAddEquiv with
    continuous_toFun := L.toLinearMap.continuous_on_pi
    continuous_invFun := L.symm.toLinearMap.continuous_on_pi }

@[simp] theorem piHomeo_apply (L : (ι → F) ≃ₗ[F] (ι → F)) (x : ι → F) : piHomeo L x = L x := rfl

variable (F ι) in

def glEquiv : GL ι F ≃* ((ι → F) ≃ₗ[F] (ι → F)) :=
  Matrix.GeneralLinearGroup.toLin.trans
    (LinearMap.GeneralLinearGroup.generalLinearEquiv F (ι → F))

variable [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] [SigmaCompactSpace F]

def piChar (L : (ι → F) ≃ₗ[F] (ι → F)) : ℝ≥0 := addEquivAddHaarChar (piHomeo L)

theorem piChar_mul (L M : (ι → F) ≃ₗ[F] (ι → F)) : piChar (L * M) = piChar L * piChar M := by
  have h : piHomeo (L * M) = (piHomeo M).trans (piHomeo L) := ContinuousAddEquiv.ext fun _ => rfl
  rw [piChar, h, addEquivAddHaarChar_trans, mul_comm]
  rfl

theorem piChar_one : piChar (1 : (ι → F) ≃ₗ[F] (ι → F)) = 1 := by
  have h : piHomeo (1 : (ι → F) ≃ₗ[F] (ι → F)) = ContinuousAddEquiv.refl _ :=
    ContinuousAddEquiv.ext fun _ => rfl
  rw [piChar, h, addEquivAddHaarChar_refl]

def glChar : GL ι F →* ℝ≥0 where
  toFun g := piChar (glEquiv F ι g)
  map_one' := by rw [map_one, piChar_one]
  map_mul' g g' := by rw [map_mul, piChar_mul]

end Pi

end WmSysEquiv

end GroundTheory.Heights₂.Theta
