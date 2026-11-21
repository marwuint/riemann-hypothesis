import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LatticeIndices.FstMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.FundamentalEquivalence.LevelIntersectParabolic

noncomputable section

namespace MassDataIdxSpl

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Matrix
open scoped TensorProduct

theorem firstProj_split_mulVec {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr1 θ (M *ᵥ v) = (M.map fun t => (θ t).1) *ᵥ pr1 θ v := by
  ext i
  simp [pr1, Matrix.mulVec, dotProduct, Prod.fst_sum]

theorem secondProj_split_mulVec {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}
    [Fintype n] (M : Matrix n n T) (v : n → T) :
    pr2 θ (M *ᵥ v) = (M.map fun t => (θ t).2) *ᵥ pr2 θ v := by
  ext i
  simp [pr2, Matrix.mulVec, dotProduct, Prod.snd_sum]

end MassDataIdxSpl
