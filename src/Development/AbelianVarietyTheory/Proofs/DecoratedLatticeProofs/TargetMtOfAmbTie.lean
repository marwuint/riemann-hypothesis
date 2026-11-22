import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
import Formalism.LocalToGlobal.Columns.ToHLatLemmas

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep

