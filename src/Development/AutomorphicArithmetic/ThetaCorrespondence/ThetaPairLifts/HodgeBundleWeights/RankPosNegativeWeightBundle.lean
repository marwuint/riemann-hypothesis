import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankPosNegativeWeightBundle
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatDegreeStatement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.FlatTensorSwapIsIso
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsCuspValueNeZeroLowLevel
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringShiftPreservesGoodAt
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
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

section
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
theorem exists_twist_ne_zero_of_lowered (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) {D : D7} (T : CoreJ D) (j : ℕ) (Y : Deep T.toCore j) (e : ℕ) (o : ℝ)
    (hT : LawsJ T) (hj : InR D j) (hY : Y.Good e o) (hF : FlatExists Y.U (xiR D))
    (u : AllWt.Weight (T.Q.Dw j)) (w₀ : Psi T.Q.H → ℤ) (m : ℕ) (Z : Comp Y.d.Xo₂ Y.d.c₂)
    {f : Rul Y.d.Xo₂ Y.d.c₂} (hf : f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) u 0)) (hf0 : f ≠ 0) :
    ∃ g ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m), g ≠ 0 := by
  have hL := _root_.GlobalTheory.LawsDeep.laws_deep D T j Y e o hT hj hY
  have hN := _root_.GlobalTheory.UnramPoint.unramPts hP.q18 hP.q1 hP.p5 _ _ _ Y.d.l₂ Y.d.Xo₂ Y.d.c₂ hL.pos
  obtain ⟨hK, ht⟩ := _root_.GlobalTheory.KeyRootSpread.exists_twSec_keyRoot_spread _ _ _ _ _ _ _ Y.U hL.unf (xiR D) hL.xi hL.geo hL.pos hL.good hN
  obtain ⟨t, ht1, ht2⟩ := ht Z
  obtain ⟨s, -, -, -, hs1, hs2⟩ := (GlobalTheory.FlatTwisting.twSec_of_flat _ _ _ _ _ _ _ Y.U (xiR D) _ hK hL.unf hL.pos hN).1 Z (-w₀) _
      (FlatSec.shift (hasPts Y.U hL.pos hL.good hL.unf Z) (fun τ => (hF.nonempty Z τ).some) (-w₀))
      ((Set.finite_iUnion fun τ => finite_flDefect_vw (Dw := T.Q.Dw j) (c := Y.d.c₂) τ).subset fun w hw => by
        by_contra hn
        simp only [Set.mem_iUnion, Function.mem_support, not_exists, not_not] at hn
        exact hw (by simp [Finset.sum_apply, hn]))
  obtain ⟨z, -, -⟩ := GlobalTheory.CombTw.exists_twSec_comb _ _ _ _ _ _ _ Y.U hL.unf (xiR D) _ Z u w₀ m _ s t hs1 hs2 ht1 ht2
  have hB : Even (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m).2 := AllWt.even_wtOf _ _
  have hf' : f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m +
      (wtOf (T.Q.Dw j) u 0 - wtOf (T.Q.Dw j) (u + parWt (T.Q.Dw j) w₀) m)) := by
    rwa [add_sub_cancel]
  refine ⟨f * z.inv, z.cusp_inv _ hB f hf', fun h0 => hf0 ?_⟩
  have h1 : idem Z * f = f := idem_mul_eq (e := exZ _ (wtOf (T.Q.Dw j) u 0)) ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩
  calc f = f * idem Z := by rw [mul_comm, h1]
    _ = f * z.inv * z.sig := by rw [← z.mul_inv, mul_comm z.sig, mul_assoc]
    _ = 0 := by rw [h0, zero_mul]
end GlobalTheory.CovTop.LowPos
end
end

