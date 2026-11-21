import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SlopeTestRemainingChoicesAlt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.FormulaAt
import Development.AbelianVarietyTheory.Definitions.Divisors.TieTest
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions GlobalTheory.BigTop GlobalTheory.BigTop.Fun GlobalTheory.SqTop NumberField

namespace GlobalTheory.BigTop.Fun.ThbTie

theorem sqRank_half {D : D7} (ij : Sq D) : sqRank D ij / 2 = GlobalTheory.FunObj.SqNum.halfRank D ij.1 ij.2 := by
  unfold sqRank GlobalTheory.FunObj.SqNum.halfRank GlobalTheory.ChiGrid.rankV
  congr 1
  ring

theorem htLe_nonneg {K : Type} [Field K] [NumberField K] [StarRing K] {g : Formalism.PairingDivisionLocalBalance.Pl K → ℤ} {z : K} {B : ℝ}
    (h : Formalism.PairingDivisionLocalBalance.HtLe g z B) : 0 ≤ B :=
  (finsum_nonneg fun w => mul_nonneg (div_nonneg (Real.log_natCast_nonneg _) (Nat.cast_nonneg _)) (abs_nonneg _)).trans h.2

theorem htLe_one_zero {K : Type} [Field K] [NumberField K] [StarRing K] {B : ℝ} (hB : 0 ≤ B) :
    Formalism.PairingDivisionLocalBalance.HtLe (fun _ => (0 : ℤ)) (1 : K) B := by
  have e : (fun w : Formalism.PairingDivisionLocalBalance.Pl K => Formalism.DivisionValues.lw w * |((Formalism.DivisionValues.vw w (1 : K) + 0 : ℤ) : ℝ)|) = fun _ => 0 := by
    funext w
    simp [Formalism.DivisionValues.ValuationRepresentative.vw_one]
  refine ⟨?_, ?_⟩
  · rw [e]
    simp
  · rw [e, finsum_zero]
    exact hB

end GlobalTheory.BigTop.Fun.ThbTie

end
