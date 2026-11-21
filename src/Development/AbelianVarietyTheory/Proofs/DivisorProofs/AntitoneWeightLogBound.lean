import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MeanLogSupNormLowerBoundCmFrameNonvanishing
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.ExistsPrincipalLattice
import Formalism.LocalToGlobal.ProjectiveLattices.L2DefiniteCuspForms
import Formalism.LocalToGlobal.ProjectiveLattices.NonnegIffOfLiesTotal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NonemptyUnitAt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.NonvanishingNearMaximum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.IsotropicCoefficientSplitting
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.OneLeAbsNormOfLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ProdMulLeDetIdeal
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ValuationLeOfEqAlgebraMap
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.AbsNormSpanGalois
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.DetValuationLeOne
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsEvalNeZeroOfTotalDegreeLt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.ExistsMonicIrreducibleCardGt
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.FiniteDetAddSmulOneEqZero
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.LargeResidueExtensionLemma
import Formalism.LocalToGlobal.CMDeterminantIdeals.CMIdealValuations.HermitianFormGramBlockBasis
import Development.AbelianVarietyTheory.Definitions.RegularCharts.BaseNorm
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedFrameSumPositive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormOneTorusClassNumberBoundProof
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DefiniteBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassBoundOfTamagawaUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SupremumConstantLogBound
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.UnitaryHaarVolume
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeepLevelCoverPrincipalLevelLawsGaloisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemSpanCuspOn
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.FiniteAndFinrankLeOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FramePointsOverComponentOpenSet
import Development.AbelianVarietyTheory.Definitions.Foundations.CanonicalExponents
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ClausesIffExistsUnique
import Formalism.LocalToGlobal.ProjectiveLattices.TieReadSS
import Formalism.LocalToGlobal.ProjectiveLattices.NormLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormRankLeBergmanBoundGoodCover
import Development.AutomorphicArithmetic.FrobeniusLocalisation.RadBounds2
import Formalism.LocalRingCardinality.HostCls
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.HostFieldGaloisDegreeDiscrConjMovesPrimes

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank

open ReciprocityTheory.ChartRestriction.G.FD

theorem abs_wtOf_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (la : AllWt.Weight Dw) (x : (E →+* ℂ) × ℕ) :
    |(((wtOf Dw la 0).1 x : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  have key : ∀ τ i, |(la τ i : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := fun τ i =>
    (Finset.single_le_sum (f := fun i => |(la τ i : ℝ)|) (fun _ _ => abs_nonneg _) (Finset.mem_univ i)).trans
      (Finset.single_le_sum (f := fun τ => ∑ i, |(la τ i : ℝ)|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _)
        (Finset.mem_univ τ))
  have h0 : (0 : ℝ) ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  unfold wtOf
  dsimp only
  split_ifs <;> push_cast <;> simp only [sub_zero, abs_neg, abs_zero] <;> first | exact h0 | exact key _ _

theorem abs_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) (τ : (U.X k).Ψ) (i : Fin r) :
    |((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)| ≤ ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  unfold AllWt.modelWt
  have h2 : (wtOf Dw la 0).2 / 2 = 0 := by rw [AllWt.wtOf_snd]; simp
  split_ifs
  · rw [h2, add_zero]; exact abs_wtOf_le la _
  · rw [h2, sub_zero]; push_cast; rw [abs_neg]; exact abs_wtOf_le la _

theorem sum_spread_modelWt_le {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Unf Xo c σ r)
    (la : AllWt.Weight Dw) (k : U.Comp) :
    ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤
      2 * (Module.finrank ℚ E : ℝ) * ∑ τ, ∑ i, |(la τ i : ℝ)| := by
  set S := ∑ τ, ∑ i, |(la τ i : ℝ)| with hS
  have h0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hsp : ∀ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ 2 * S := by
    intro τ
    unfold Data.spread
    rcases isEmpty_or_nonempty (Fin r) with hr | hr
    · simp [Real.iSup_of_isEmpty, Real.iInf_of_isEmpty]; linarith
    · have hb := fun i => abs_le.1 (abs_modelWt_le U la k τ i)
      have h1 : (⨆ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ)) ≤ S := ciSup_le fun i => (hb i).2
      have h2 : -S ≤ ⨅ i, ((AllWt.modelWt U (wtOf Dw la 0) k τ i : ℤ) : ℝ) := le_ciInf fun i => (hb i).1
      linarith
  have hcard : (Fintype.card (U.X k).Ψ : ℝ) ≤ Module.finrank ℚ E := by
    have e1 : Fintype.card (U.X k).Ψ = (U.X k).Ψ.card := Fintype.card_coe _
    have e2 : (U.X k).Ψ.card ≤ Fintype.card (E →+* ℂ) := Finset.card_le_univ _
    rw [NumberField.Embeddings.card] at e2
    exact_mod_cast e1 ▸ e2
  calc ∑ τ, (U.X k).spread (AllWt.modelWt U (wtOf Dw la 0) k) τ ≤ ∑ _τ : (U.X k).Ψ, 2 * S :=
        Finset.sum_le_sum fun τ _ => hsp τ
    _ = (Fintype.card (U.X k).Ψ : ℝ) * (2 * S) := by rw [Finset.sum_const, nsmul_eq_mul]; rfl
    _ ≤ (Module.finrank ℚ E : ℝ) * (2 * S) := mul_le_mul_of_nonneg_right hcard (by linarith)
    _ = _ := by ring

end GlobalTheory.BergRank

namespace GlobalTheory.BergRank

end GlobalTheory.BergRank
