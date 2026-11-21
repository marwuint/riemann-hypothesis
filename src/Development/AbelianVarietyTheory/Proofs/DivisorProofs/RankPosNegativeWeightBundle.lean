import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
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
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoreGoodMatch
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatLineC1LogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Definitions.Divisors.UnifOfSpaceEq
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ComponentMassSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightConditionsAtIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodAtOfAntitoneGapWeight
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsKeySectionInverseRootTwistingSectionSpread
import Development.AbelianVarietyTheory.Definitions.Divisors.EightDvdNCol
import Development.AbelianVarietyTheory.Definitions.Divisors.CongModRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplexUniformizationLawsOfGoodDeepCover
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasUnramifiedIntegralFramedPointsOfGoodPlaces
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.FormalAlgebraisation
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomogeneousCompIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KchMul
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FibreFramesOnModels
import Formalism.LocalToGlobal.ProjectiveLattices.CuspidalL2Subspace
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CanonicalOfAbelianDeRham
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTwSecOfConst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMulInvPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsNumberFieldPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan

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

namespace GlobalTheory.CovTop.LowPos

open GlobalTheory.FlatTw GlobalTheory.FlatLine

theorem rk_pos {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {G : WTZ D.host.E} (h : Y.GoodAt G)
    {f : Rul Y.d.Xo₂ Y.d.c₂} (hf : f ∈ Y.V G) (hf0 : f ≠ 0) : 0 < Y.rk G := by
  haveI : Module.Finite Y.d.c₂.F (Y.V G) := Module.Finite.of_basis h.1.some.2.1.1
  show 0 < Module.finrank Y.d.c₂.F (Submodule.span Y.d.c₂.F (latW Y.U G : Set (Y.V G)))
  rw [h.2.2, finrank_top]
  exact Module.finrank_pos_iff_exists_ne_zero.2 ⟨⟨f, hf⟩, fun e => hf0 (congrArg Subtype.val e)⟩

theorem mem_cuspW_of_exZ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E}
    {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r}
    (hU : ∀ σ, GoodEmb c σ → IsUnf (U σ)) {G G' : WTZ E} (h : exZ Dw G = exZ Dw G') {f : Rul Xo c}
    (hf : f ∈ cuspW Xo c U G) : f ∈ cuspW Xo c U G' := by
  rw [AllWt.mem_cuspW] at hf ⊢
  refine ⟨h ▸ hf.1, fun σ hσ => ?_⟩
  rw [← AllWt.modelWt_congr (U σ) hσ (hU σ hσ) h]
  exact hf.2 σ hσ

theorem exZ_lowered {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)
    (a : (E →+* ℂ) × ℕ → ℕ) (n kc : ℕ) (c0 : ℤ) (hn : Even n) :
    exZ Dw (wtOf Dw (uMinus Dw a n kc c0 + parWt Dw (anchor Dw a n kc)) ((n / 2 : ℕ) : ℤ)) = exZ Dw (shiftG Dw a n (-c0)) := by
  obtain ⟨m, rfl⟩ := hn
  have h2 : m + m = 2 * m := by ring
  rw [h2, Nat.mul_div_cancel_left m two_pos, GlobalTheory.CovTop.Model.exZ_shiftG]
  show exZ Dw (wtOf Dw _ _) = exZ Dw (wtOf Dw _ _)
  congr 2
  rw [uMinus, ← uWt_add_anchor Dw a (2 * m) kc, neg_smul]
  abel

end GlobalTheory.CovTop.LowPos
