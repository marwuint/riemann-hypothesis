import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
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
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Definitions.CMLattices.IntegralOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightLatticeSpanEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatWFgPow

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.CovTop.ShiftGood

variable {D : D7} {T : Core D} {j : ℕ}

theorem cuspW_eq_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') : Y.V G = Y.V G' := by
  ext f
  rw [GlobalTheory.AllWt.mem_cuspW, GlobalTheory.AllWt.mem_cuspW, h]
  refine and_congr_right fun _ => forall₂_congr fun σ hσ => ?_
  rw [GlobalTheory.AllWt.modelWt_congr (Y.U σ) hσ (hY.unf σ hσ) h]

theorem goodAt_of_exZ {Y : Deep T j} {e : ℕ} {o : ℝ} (hY : Y.Good e o) {G G' : WTZ D.host.E}
    (h : exZ (T.Q.Dw j) G = exZ (T.Q.Dw j) G') (hG : Y.GoodAt G) : Y.GoodAt G' := by
  refine ⟨hasGram_nrm_of_good D T j Y e o hY G', ?_⟩
  have key : ∀ C C' : Submodule Y.d.c₂.F (Rul Y.d.Xo₂ Y.d.c₂), C = C' →
      ((GlobalTheory.AllWt.supLat C).FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C : Set C) = ⊤) →
      ((GlobalTheory.AllWt.supLat C').FG ∧ Submodule.span Y.d.c₂.F (GlobalTheory.AllWt.supLat C' : Set C') = ⊤) := by
    rintro C _ rfl; exact id
  exact key _ _ (cuspW_eq_of_exZ hY h) hG.2

end GlobalTheory.CovTop.ShiftGood

namespace GlobalTheory.CovTop.ShiftGood

end GlobalTheory.CovTop.ShiftGood

end
