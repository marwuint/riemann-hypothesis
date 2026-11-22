import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodCompNonempty
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ToroidalFlagProportionalityOfGoodChernWeilStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalFlagNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlagSpaceComponentSmoothProjectiveConnected
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspFormsExtendVanishCompactifiedFlagSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToroidalIntegralWeightSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.CovTop.LowNonzero

theorem gapGe_wt_add_parWt {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} (P : WtPar Dw) (hB : WtBig P) (j : ℕ) (w : Psi H → ℤ) :
    GapGe (((FlagTan.dimFlag Dw + 1).choose 2 + 1 : ℕ) : ℤ) (P.wt j + GlobalTheory.FlatLine.parWt Dw w - FlagTan.kap Dw) := by
  intro τ k hk
  have a := (gaps_of_wtBig _ _ _ P hB P.u₁ (by simp)).1 τ k hk
  have hg := hB.gaps τ k hk
  have b := (P.gap_rem τ k).1
  have c : gap (GlobalTheory.FlatLine.parWt Dw w τ) k = 0 := by
    simp [gap, GlobalTheory.FlatLine.parWt]
  have hC0 : (0 : ℤ) ≤ (((FlagTan.dimFlag Dw + 1).choose 2 : ℕ) : ℤ) := Int.natCast_nonneg _
  have hD0 : (0 : ℤ) ≤ (FlagTan.dimFlag Dw : ℤ) := Int.natCast_nonneg _
  have hp0 : (0 : ℤ) ≤ (Dw.p : ℤ) := Int.natCast_nonneg _
  have hq0 : (0 : ℤ) ≤ (Dw.q : ℤ) := Int.natCast_nonneg _
  have e1 := mul_nonneg hD0 (le_trans zero_le_one a)
  have e2 := mul_nonneg (Int.natCast_nonneg j) (le_trans zero_le_one a)
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, gap_add, gap_sub, gap_nsmul, c]
  push_cast at hg ⊢
  nlinarith [mul_nonneg hD0 hC0, mul_nonneg hD0 hp0, mul_nonneg hD0 hq0, mul_nonneg hD0 hD0]

open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.Vanishing.H0 ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory in

theorem ne_zero_of_noBase {k : Type} [Field k] {Y : Scheme.{0}} {p : Y ⟶ Sp k} {B : LB Y} {hB : B.IsLB}
    {W : Submodule k (H0 p B ⊤)} {U : Y.Opens} (h : NoBase hB W U) (hU : (U : Set Y).Nonempty) : ∃ f ∈ W, f ≠ 0 := by
  obtain ⟨y, hy⟩ := hU
  by_contra hne
  push Not at hne
  refine h y hy ((mem_support_baseIdeal hB W y).2 fun s hs hy' => ?_)
  obtain ⟨i, hi⟩ := exists_chart hB y
  have hu := (isUnit_ger_iff _ hi).2 hy'
  rw [ger_toSec, hne s hs, map_zero] at hu
  exact not_isUnit_zero hu

end GlobalTheory.CovTop.LowNonzero

end
