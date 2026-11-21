import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open GlobalTheory.SplitFlip
open scoped Matrix

namespace GlobalTheory.FullRankCoinv

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

variable (k) in

def Y0 (n d : ℕ) : Matrix (Fin n) (Fin d) k := Matrix.of fun i j => if (j : ℕ) = d - n + i then 1 else 0

end GlobalTheory.FullRankCoinv
