import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeStableAlmostAllPlacesRight

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (F) in

def idemInf : AF F := LinearMap.inl F (Ainf F) (Af F) 1

theorem evI_eq (a : AF F) : evI F a = InfiniteAdeleRing.ringEquiv_mixedSpace F (fstA F a) := rfl

end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mixM {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  e • G + (1 - e) • 1

variable {σ : E →ₐ[F] E}

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) : mat (x * y) = mat x * mat y := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

end GlobalTheory.UnitaryTriSplit

namespace GlobalTheory.UnitaryTriSplit
end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

end GlobalTheory.UnitaryTriSplit
