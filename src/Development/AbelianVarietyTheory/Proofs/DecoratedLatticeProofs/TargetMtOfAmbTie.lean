import Mathlib
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction
import Formalism.LocalToGlobal.Divisibility.ProjLemmas
import Formalism.LocalToGlobal.GlobalTheory.HLatOpsP
import Formalism.LocalRingCardinality.DataArith
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsIsConjAtOfEmbedding
import Formalism.HarderNarasimhan.ShiftInvariance
import Formalism.HarderNarasimhan.HarderNarasimhanProofs.PolygonSlopeSum
import Formalism.HarderNarasimhan.Statement
import Formalism.QuotientMetricDivisors.ReductionLemmaZero
import Formalism.QuotientMetricDivisors.FinalW
import Formalism.LocalToGlobal.Divisibility.FramesLemmas
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NegLogLeLcvOfIntegralForm
import Formalism.LocalToGlobal.Columns.ToHLatLemmas
import Formalism.LocalToGlobal.Columns.RowFormsGood
import Formalism.LocalToGlobal.Divisibility.ClassSumBridge

open Module NumberField Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Rows Formalism.L2.Indef
open scoped Matrix ComplexOrder

namespace GlobalTheory.Core.AmbTieStep

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dot {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

end GlobalTheory.Core.AmbTieStep

