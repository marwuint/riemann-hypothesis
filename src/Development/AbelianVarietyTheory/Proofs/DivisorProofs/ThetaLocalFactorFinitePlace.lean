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

theorem fstA_idemInf : fstA F (idemInf F) = 1 := rfl

theorem fstA_idemAt (w : Pl F) : fstA F (idemAt w) = 0 := rfl

end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

open Matrix GlobalTheory.UnitaryPlaceSplit

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def mixM {n : ℕ} (e : AF F) (G : Matrix (Fin n) (Fin n) (AE F E)) : Matrix (Fin n) (Fin n) (AE F E) :=
  e • G + (1 - e) • 1

theorem mixM_one_right {n : ℕ} (e : AF F) : mixM e (1 : Matrix (Fin n) (Fin n) (AE F E)) = 1 := by
  rw [mixM, ← add_smul, add_sub_cancel, one_smul]

theorem mixM_mul_same {n : ℕ} {e : AF F} (he : e * e = e) (G G' : Matrix (Fin n) (Fin n) (AE F E)) :
    mixM e G * mixM e G' = mixM e (G * G') := by
  rw [mixM, mixM, mixM, mix_mul he, mul_one]

variable {σ : E →ₐ[F] E}

theorem mixM_mem {n : ℕ} {J : Matrix (Fin n) (Fin n) E} {e : AF F} (he : e * e = e) (g : UA σ J) :
    (mixM e (mat g))ᵀ * incM F J * (mixM e (mat g)).map (cA σ) = incM F J := by
  have hg : (mat g)ᵀ * incM F J * (mat g).map (cA σ) = incM F J := g.2
  have split : ∀ X : Matrix (Fin n) (Fin n) (AE F E), X = e • X + (1 - e) • X := fun X => by
    rw [← add_smul, add_sub_cancel, one_smul]
  have hT : (mixM e (mat g))ᵀ = e • (mat g)ᵀ + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [mixM, transpose_add, transpose_smul, transpose_smul, transpose_one]
  have hc : (mixM e (mat g)).map (cA σ) = e • (mat g).map (cA σ) + (1 - e) • (1 : Matrix (Fin n) (Fin n) (AE F E)) := by
    rw [← AlgHom.mapMatrix_apply, mixM, map_add, map_smul, map_smul, map_one, AlgHom.mapMatrix_apply]
  rw [hT, hc, split (incM F J), mix_mul he, mix_mul he, hg, one_mul, mul_one]

def mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) : UA σ J :=
  ⟨⟨mixM e (mat g), mixM e (mat g⁻¹),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.mul_inv g.1)).trans (mixM_one_right e),
    by rw [mixM_mul_same he]; exact (congrArg (mixM e) (Units.inv_mul g.1)).trans (mixM_one_right e)⟩,
    mixM_mem he g⟩

theorem mat_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g) = mixM e (mat g) := rfl

theorem mat_inv_mixU {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (e : AF F) (he : e * e = e) (g : UA σ J) :
    mat (mixU e he g)⁻¹ = mixM e (mat g⁻¹) := rfl

theorem mat_mul {n : ℕ} {J : Matrix (Fin n) (Fin n) E} (x y : UA σ J) : mat (x * y) = mat x * mat y := rfl

theorem mat_one {n : ℕ} {J : Matrix (Fin n) (Fin n) E} : mat (1 : UA σ J) = 1 := rfl

end GlobalTheory.UnitaryTriSplit

namespace GlobalTheory.UnitaryTriSplit
end GlobalTheory.UnitaryTriSplit

noncomputable section

namespace GlobalTheory.UnitaryTriSplit

end GlobalTheory.UnitaryTriSplit
