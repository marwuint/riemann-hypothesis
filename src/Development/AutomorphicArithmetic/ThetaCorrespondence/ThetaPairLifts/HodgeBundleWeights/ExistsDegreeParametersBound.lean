import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDegreeParametersBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AbelianVarietyTheory.Definitions.Divisors.HypothesesX
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
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
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ToroidalChartsForFan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogFinrankCuspFormsLe
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.BinomialFlagDimensionDegreeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.IntegralCuspSlopePowerBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCuspFrameWeights
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ShortGeneratorNormComparison
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BirationalOnWeightParameters
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeBasisPeterssonSecond
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HermitianGeometricHypothesisHolds

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
set_option autoImplicit false
namespace GlobalTheory.HSShortRun
open GlobalTheory.Vanishing GlobalTheory.Adelic GlobalTheory.HilbertSamuel GlobalTheory.HSCore
variable {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j}
theorem hilbertSamuel_estimate_at_level (hP : _root_.GlobalTheory.CovTop.Hypotheses'') (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : Quoted)
    (hN : GlobalTheory.Published.NadelVanishingAndNonKltDivisor) (hPr : GlobalTheory.Published.Principalisation)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hC : GlobalTheory.Published.ToroidalChartsForFan)
    (hL : GlobalTheory.Published.SemiAbelianLieSeminegative) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (hE : 2 < Module.finrank ℚ D.host.E / 2) (Z : Comp Y.d.Xo₂ Y.d.c₂) {P : WtPar (T.Q.Dw j)} (hW : WtBig P)
    (hA : ∀ i ≤ P.T, Y.GoodAt (wtOf _ (P.wt i) 0)) {PP κ : ℝ} (hPP : 0 ≤ PP) (hκ : 0 ≤ κ)
    (f₂ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₂)
    (f₁ : CuspFrame Z Y.U (xiR D) (fun _ => D.sp.W j) Y.dict P.u₁) {Λ β : ℝ} (hΛ : 1 ≤ Λ) (hβ : 1 ≤ β)
    (hfr : ∀ q σ, ChowHt.frameNorm (f₁.A σ) (fun a => σ (f₁.w.col q a)) ≤ Λ)
    (hberg : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict P.u₁ β)
    (hBir : BirOn Y.U Z (wtOf _ P.u₁ 0) ∧ BirOn Y.U Z (wtOf _ P.u₂ 0))
    (h0 : ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt 0)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt 0) 0) σ (v q).1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)))
    (hsh : ∀ i ≤ P.T, ∃ (m : ℕ) (v : Fin m → Cusp Z Y.U (P.wt i)), (∀ q, v q ∈ latOn Y.U Z _) ∧
      Submodule.span Y.d.c₂.F (Set.range v) = ⊤ ∧ ∀ q σ, petOn Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z
        (wtOf _ (P.wt i) 0) σ (v q).1 ≤ Real.exp (PP * κ)) :
    1 ≤ (f₁.n : ℝ) ∧ Formalism.NormVectorIdentities.Items.HSClaimS 26 P.T (CompHt.dimFlag (T.Q.Dw j)) f₁.n 1 Λ β (Real.exp (PP * κ))
      (Real.exp (PP * κ)) (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) (Y.dg P.u₁ Z) (Y.ht P.u₁ Z)
      (Y.rkC (P.wt P.T) Z) (Y.degC (P.wt P.T) Z) := by
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z P hW hA
  have hPk : 0 ≤ PP * κ := mul_nonneg hPP hκ
  let k : Consts := ⟨Λ, β, Real.exp (PP * κ), Real.exp (PP * κ), 0, hβ, Real.one_le_exp hPk, Real.one_le_exp hPk⟩
  let th : R.L.Sec := 0
  have r₁ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hBir.1
  have r₂ := GlobalTheory.T.cuspForm_ratios_generate_at_flagSpace_genericPoint TF.X Z Y.U P.u₂ ⟨R.toModif⟩ hBir.2
  have hΛ₀ : 1 ≤ Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1)) := Real.one_le_exp (by positivity)
  have sh : ∀ i ≤ P.T, (h.data f₁ f₂ th k).ShortFamily i (Real.exp (PP * κ)) := fun i hi => by
    obtain ⟨m, v, l, s, n⟩ := hsh i hi
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k i hi _ m v l s n
  have s0 : (h.data f₁ f₂ th k).ShortFamily 0 (Real.exp (CompHt.dimFlag (T.Q.Dw j) * PP * (κ / P.T + 1))) := by
    obtain ⟨m, v, l, s, n⟩ := h0
    exact GlobalTheory.HSApp.shortFamily_of_spanning _ _ _ _ _ _ TF Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k 0 P.T.zero_le _ m v l s n
  have hDT : FlagTan.dimFlag (T.Q.Dw j) ≤ P.T := (Nat.le_succ _).trans h.le_T
  have hyp := _root_.GlobalTheory.T.hermitian_geometric_hypothesis_holds hP hG hQ hN hPr hS hC hL D T j Y e o hY hE Z TF P R ω h f₁ f₂ th k _ hW r₁ r₂ hberg hΛ hfr hΛ₀ s0
    (sh _ hDT) (sh _ le_rfl)
  have hC := _root_.GlobalTheory.HSShort.hsClaimS_component_geo hQ _ _ _ _ _ _ _ TF.X Z _ Y.U P R ω _ _ _ _ h f₁ f₂ th k _ hyp
  have hrk : Y.rkC (P.wt P.T) Z = Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
    show ((Formalism.HN.rkK _ : ℕ) : ℝ) = _
    rw [Formalism.HN.rkK, (h.good _ le_rfl).2.2, finrank_top]
  rw [Real.log_exp] at hC
  refine ⟨by exact_mod_cast (h.geo f₁ f₂ th k).one_le_n, ?_⟩
  rw [hrk]
  exact hC
end GlobalTheory.HSShortRun
end

