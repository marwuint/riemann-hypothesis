import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IotaScalarOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusOfPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TiltIsDomainValuationRing

open GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.SandwichMaps GlobalTheory.DetInv Matrix TensorProduct

noncomputable section

namespace GlobalTheory.LemYR

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O] {Λ : Type} [CommRing Λ] [Algebra ℤ_[p] Λ]

def phiT : RL p O Λ →+* RL p O Λ :=
  (Algebra.TensorProduct.map (PsiPhi.frobAlg (p := p) (O := O)) (AlgHom.id ℤ_[p] Λ)).toRingHom

theorem phiT_tmul (a : Ainf p O) (l : Λ) : phiT (a ⊗ₜ l) = WittVector.frobenius a ⊗ₜ l := rfl

end GlobalTheory.LemYR

