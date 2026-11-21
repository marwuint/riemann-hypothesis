import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeLFunctionBottomPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareBottomHalfRankSumLeHalfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StdMassNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockIpSelfRePos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacNormNeZero

open Finset
open GlobalTheory.SqTop GlobalTheory.FunObj.SqNum
open GlobalTheory.NormSum (Pair)
open GlobalTheory.CMVal (IsHeckeL)

namespace GlobalTheory.NormBigProof

theorem squareBottomHalfRankSum_le_halfRank (D : Formalism.BasicNotions.D7) (i j : ℕ) : h0 D i j ≤ halfRank D i j := by
  unfold h0 halfRank botBig botSmall
  exact Nat.div_le_div_right (Nat.add_le_add (Nat.sub_le _ _) (Nat.sub_le _ _))

end GlobalTheory.NormBigProof
