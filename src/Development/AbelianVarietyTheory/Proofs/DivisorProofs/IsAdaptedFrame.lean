import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKernelReal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolEqISupFockDeg
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

open scoped TensorProduct Matrix Classical
open NumberField Formalism.BasicNotions.TH GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RealLift

namespace GlobalTheory.FockBridge

section Fock

variable {F : Type} [Field F] [NumberField F] {P : Type} [AddCommGroup P] [Module ℂ P] {p₁ q₁ r s : ℕ}

variable (r s) in

def negT : Mat r s →ₗ[ℂ] Mat r s where
  toFun Y := -Yᵀ
  map_add' Y Z := by rw [Matrix.transpose_add, neg_add]
  map_smul' c Y := by rw [Matrix.transpose_smul, RingHom.id_apply, smul_neg]

end Fock

end GlobalTheory.FockBridge
