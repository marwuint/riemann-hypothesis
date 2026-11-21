import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeySectionValuationBoundsDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionFourthRootPerComponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitSectionThetaKeyRuleWeightFour
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.KeyFamOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrdConjDifferentEqZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaKeyRuleValuationNonnegIntegralFramedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstantSmulIntegralOfFourthPowerStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsParallelWeightInvertibleSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyWeightSectionProducts
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDominantExponentsMatchingWeightBarGap
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.GeometryOfNumbersTheory TopologicalSpace Limits
open GlobalTheory.HSApp
open GlobalTheory.LamT (CMPt)
set_option synthInstance.maxHeartbeats 400000

noncomputable section
namespace GlobalTheory.WtMatchBar

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

theorem pow_mem_secZ {ex : Ix Dw → ℤ} {f : Rul Xo c} (hf : f ∈ GlobalTheory.AllWt.secZ Xo c ex) (n : ℕ) :
    f ^ n ∈ GlobalTheory.AllWt.secZ Xo c (n • ex) := by
  induction n with
  | zero => rw [pow_zero, zero_smul]; exact GlobalTheory.AllWt.one_mem_secZ
  | succ n ih => rw [pow_succ, succ_nsmul]; exact GlobalTheory.AllWt.mul_mem_secZ ih hf

theorem nsmul_exOf_zero_one (m : ℕ) : m • GlobalTheory.AllWt.exOf Dw 0 1 = GlobalTheory.AllWt.exOf Dw 0 m := by
  induction m with
  | zero => rw [zero_smul]; funext i; rw [Nat.cast_zero, GlobalTheory.AllWt.exOf, GlobalTheory.AllWt.wtOf_zero]; cases i <;> rfl
  | succ m ih =>
    rw [succ_nsmul, ih, ← GlobalTheory.AllWt.exOf_add, add_zero]; push_cast; rfl

theorem val_pow_succ_nonneg {la : IsDedekindDomain.HeightOneSpectrum (𝓞 c.F)} {v : Rul Xo c → EReal}
    (hv : IsVal la v) {f : Rul Xo c} (hf : 0 ≤ v f) (n : ℕ) : 0 ≤ v (f ^ (n + 1)) := by
  induction n with
  | zero => rw [pow_one]; exact hf
  | succ n ih => rw [pow_succ, hv.mul]; exact add_nonneg ih hf

end GlobalTheory.WtMatchBar
