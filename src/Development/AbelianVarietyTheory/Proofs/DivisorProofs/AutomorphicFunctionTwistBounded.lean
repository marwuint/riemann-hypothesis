import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLeviLeviElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLeviElementAdapted
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdaptedPlaneIntegralSkewHermitianTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicConstantTermParabolic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothLocalLieRepresentation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.QdetPolyMapMonic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CapCommuteRtInfGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoeffMemSubmoduleOfComplexPolyValuesMem
import Development.AbelianVarietyTheory.Definitions.Foundations.EqPlaceIdemOfIsPrimeIdem

noncomputable section
namespace GlobalTheory.TorFin
open Matrix
open scoped ContDiff

section Mat
variable {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} {x y : Fin n → ℂ}

theorem IsSkew.exp (hd : IsUnit J.det) {Z : Matrix (Fin n) (Fin n) ℂ} (hZ : IsSkew J Z) (t : ℝ) :
    IsUni J (NormedSpace.exp (t • Z)) := by
  refine GlobalTheory.SmoothForms.exp_mem_UH hd ?_
  have : Zᴴ * J + J * Z = 0 := hZ
  rw [conjTranspose_smul, star_trivial, smul_mul_assoc, mul_smul_comm, ← smul_add, this, smul_zero]

end Mat

end GlobalTheory.TorFin
end

namespace GlobalTheory.TorFin
end GlobalTheory.TorFin
namespace GlobalTheory.TorFin
end GlobalTheory.TorFin
