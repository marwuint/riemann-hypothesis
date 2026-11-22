import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BinomialFlagDimensionDegreeBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.WeightPrincipalisationBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringDomainLatticeRegularity
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsWeightHodgeBundleGenerated
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.HodgeBundleIsNefIsBigOfWeight

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
noncomputable section
namespace GlobalTheory.CovTop.DgShare
theorem nef_share_lower_bound (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hSi : GlobalTheory.Published.SiegelToroidalIntegral) (hFa : GlobalTheory.Published.ToroidalChartsForFan) (hSA : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7} {T : CoreJ D}
    (hT : LawsJ T) {j : ℕ} (hp : 1 ≤ (T.Q.Dw j).p) (hq : 1 ≤ (T.Q.Dw j).q) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (P : WtPar (T.Q.Dw j)) (hB : WtBig P)
    (Z : Comp Y.d.Xo₂ Y.d.c₂) (hbir : BirOn Y.U Z (wtOf _ P.u₁ 0)) :
    (P.T - 1).choose (CompHt.dimFlag (T.Q.Dw j)) * CompHt.compDeg Y.U Z (wtOf _ P.u₁ 0) ≤
      Module.finrank Y.d.c₂.F (cuspOn Y.U Z (wtOf _ (P.wt P.T) 0)) := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨g1, g2, g3⟩ := gapGe_of_wtBig hB
  have good : ∀ la, GapGe 1 la → _ := fun la h =>
    _root_.GlobalTheory.T.covering_domain_lattice_regularity hP D T hT j hp hq hf hj Y e o hY la (antitone_of_gapGe hp hq h).1
      (antitone_of_gapGe hp hq h).2
  obtain ⟨TF, R, ω, h⟩ := _root_.GlobalTheory.T.exists_weight_hodge_bundle_generated hP1 hG hQ hP.q15 hP.q16 hSi hFa hSA D T.toCore j Y e o hY hf Z P hB fun i _ => (good _ (g3 i)).1
  obtain ⟨f₁⟩ := nonempty_cuspFrame ((good _ g1).2 Z)
  obtain ⟨f₂⟩ := nonempty_cuspFrame ((good _ g2).2 Z)
  let k : CompHS.Consts := ⟨1, 1, 1, 1, 1, le_rfl, le_rfl, le_rfl⟩
  let th : R.L.Sec := GlobalTheory.CompHS.toSec (R.Δ₁.lift 0)
  obtain ⟨a1, a2⟩ := _root_.GlobalTheory.T.hodge_bundle_isNef_isBig_of_weight hP1 hP.q7 hSi hFa hSA _ _ _ _ _ _ TF Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k hY.geo hB
  have a3 := birational_of_ratGen TF.X Z Y.U P R ω _ _ _ h f₁ f₂ th k
    (ratGen_of_birOn TF.X Z Y.U P.u₁ ⟨R.toModif⟩ hbir)
  exact GlobalTheory.HSCore.CompShare.choose_mul_compDeg_le hQ _ _ _ _ _ _ _ _ Z _ Y.U P R ω _ D _ _ h f₁ f₂ th k a1 a2 a3
end GlobalTheory.CovTop.DgShare
end
end

