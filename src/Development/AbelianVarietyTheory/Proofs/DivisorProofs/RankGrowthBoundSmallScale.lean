import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChooseAddLePowMulChooseAdd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulEqOfGenericUniqueComplexPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightPositivityPrincipalisationDeep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComponentImageDegreeBetweenOfProportionality
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformisationComponentsCovolumeEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankComponentWeightInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatConstantBoundedByNine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ValuationMultiplicityWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompositumIntermediateFieldExistsPlaceValuationE
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFieldUnramifiedCurve
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFramedPointLiesOnComponentCmCurveFieldStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIntegralFramedPointCompletionIndexOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineThetaRootTwistTwistingSection

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.HodgeSteps

theorem exists_jet_order (d T : ℕ) (ρ : ℝ) (hd : 2 ≤ d) (hT : 1000 * (d : ℝ) ^ 2 ≤ T) (h0 : 0 ≤ ρ)
    (hz : 7 * ((d : ℝ) ^ 2 / T + d * ρ) ≤ 1 / 2) :
    ∃ a : ℕ, ((T + d + 4 : ℕ) : ℝ) < (a + 1) * (1 - ρ) ∧
      (((a + d).choose d : ℕ) : ℝ) ≤ (1 + 7 * ((d : ℝ) ^ 2 / T + d * ρ)) * (((T - 1).choose d : ℕ) : ℝ) := by
  have hd' : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hTd : 2000 * (d : ℝ) ≤ T := by nlinarith
  have hT0 : (0 : ℝ) < T := by linarith
  have h1 : 0 ≤ (d : ℝ) ^ 2 / T := by positivity
  have h2 : (d : ℝ) * ρ ≤ 1 / 14 := by linarith
  have h3 : ρ ≤ 1 / 28 := by nlinarith
  have h4 : 0 < 1 - ρ := by linarith
  refine ⟨⌊((T : ℝ) + d + 4) / (1 - ρ)⌋₊, ?_, ?_⟩
  · have := Nat.lt_floor_add_one (((T : ℝ) + d + 4) / (1 - ρ))
    rw [div_lt_iff₀ h4] at this
    push_cast
    exact this
  · refine (GlobalTheory.choose_rank_ratio_le d T _ ρ hd (by exact_mod_cast (by linarith : 20 * (d : ℝ) ≤ T)) h0 (by linarith)
      (Nat.floor_le (by positivity)) ?_).trans (mul_le_mul_of_nonneg_right ?_ (by positivity))
    · rw [div_le_iff₀ (mul_pos h4 (by linarith))]
      have a1 : (d : ℝ) * ρ * T ≤ 1 / 14 * T := mul_le_mul_of_nonneg_right h2 hT0.le
      have a2 : 27 / 28 * (1999 / 2000 * (T : ℝ)) ≤ (1 - ρ) * (T - d) :=
        mul_le_mul (by linarith) (by linarith) (by positivity) h4.le
      nlinarith
    · have : 0 ≤ (d : ℝ) * ρ := by positivity
      rw [mul_div_assoc]
      linarith

theorem le_gap_bar {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (u : AllWt.Weight Dw) (τ : Psi H) (hu : Antitone (u τ)) (t : ℤ) :
    t ≤ gap (u τ + t • hodgeWt Dw τ) (Dw.p - 1) := by
  have h := hu (show (⟨Dw.p - 1, by omega⟩ : Fin (Dw.p + Dw.q)) ≤ ⟨Dw.p - 1 + 1, by omega⟩ from Nat.le_succ _)
  rw [gap, dif_pos (by omega)]
  simp only [hodgeWt, CompHt.barWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  rw [if_pos (by omega), if_neg (by omega)]
  linarith

theorem bir_gap_le (d N : ℕ) (hd : 3 ≤ d) : (d + 3) ^ 2 + 2 * N ≤ (d + 3) * ((d + 1).choose 2 + 4 * N + d + 3) := by
  nlinarith [Nat.zero_le ((d + 1).choose 2), Nat.zero_le N]

end GlobalTheory.CovTop.HodgeSteps
