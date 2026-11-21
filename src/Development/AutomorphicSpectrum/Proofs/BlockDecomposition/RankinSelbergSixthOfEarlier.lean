import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open MeasureTheory Matrix Filter Topology
open GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open GroundTheory.Automorphic.GodementSectionLocal (box mem_box isCompact_box isClopen_box modPow modPow_mul modPow_add schwartzBruhat2 slice localSection localZeta_mul_right vecMul_zero_cons)
open scoped ValuativeRel ENNReal ComplexConjugate
open Ad3 Ad3.R

namespace GlobalTheory.CompanionTheory.RankinSelberg.Trilinear

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  [MeasurableSpace F] [BorelSpace F]

def rowHomeo (κ : GL (Fin 2) F) : (Fin 2 → F) ≃ₜ (Fin 2 → F) where
  toFun r := r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)
  invFun r := r ᵥ* ((κ⁻¹ : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F)
  left_inv r := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.vecMul_one]
  right_inv r := by
    simp only [Matrix.vecMul_vecMul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.vecMul_one]
  continuous_toFun := Continuous.matrix_vecMul continuous_id continuous_const
  continuous_invFun := Continuous.matrix_vecMul continuous_id continuous_const

@[simp] theorem rowHomeo_apply (κ : GL (Fin 2) F) (r : Fin 2 → F) :
    rowHomeo κ r = r ᵥ* (κ : Matrix (Fin 2) (Fin 2) F) := rfl

def polarMeas : Measure Fˣ :=
  (multHaar F).withDensity fun z => ENNReal.ofReal ((modulus (z : F) : ℝ) ^ 2)

def rowHomeo2 (κ : GL (Fin 2) F) : (Fin 2 → F) × (Fin 2 → F) ≃ₜ (Fin 2 → F) × (Fin 2 → F) :=
  (rowHomeo κ).prodCongr (rowHomeo κ)

@[simp] theorem rowHomeo2_apply (κ : GL (Fin 2) F) (q : (Fin 2 → F) × (Fin 2 → F)) :
    rowHomeo2 κ q = (q.1 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F), q.2 ᵥ* (κ : Matrix (Fin 2) (Fin 2) F)) := rfl

instance instSFinitePolarMeas : SFinite (polarMeas (F := F)) := by
  unfold polarMeas
  infer_instance

instance sigmaFinite_plane_measure (ψ : AddChar F Circle) : SigmaFinite (m2 ψ) := by
  unfold m2
  infer_instance

end GlobalTheory.CompanionTheory.RankinSelberg.Trilinear

end
