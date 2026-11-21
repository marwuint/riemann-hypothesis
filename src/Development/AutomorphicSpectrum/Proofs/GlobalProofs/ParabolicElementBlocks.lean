import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.InstBorelGL
open MeasureTheory Matrix GlobalTheory.CompanionTheory.QL
open scoped ComplexConjugate ValuativeRel

namespace GlobalTheory.CompanionTheory.QLB

section Alg

variable {F : Type} [Field F]

theorem pEl_coe {r c : ℕ} (m₁ : GL (Fin r) F) (B : Matrix (Fin r) (Fin c) F) (m₂ : GL (Fin c) F) :
    (pEl m₁ B m₂ : Matrix (Fin (r + c)) (Fin (r + c)) F) =
      Matrix.reindex finSumFinEquiv finSumFinEquiv
        (Matrix.fromBlocks (m₁ : Matrix (Fin r) (Fin r) F) B 0 (m₂ : Matrix (Fin c) (Fin c) F)) := rfl

end Alg

end GlobalTheory.CompanionTheory.QLB
