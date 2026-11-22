import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroCuspForm
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.CoveringTopologyRefinement
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToroidalFlagNonempty
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.GloballyGeneratedOnOpenOfWeightGapGe

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
set_option synthInstance.maxHeartbeats 400000
noncomputable section
namespace GlobalTheory.CovTop.LowNonzero
theorem exists_cusp_value_ne_zero_low_level (hP : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems) (hG : GlobalTheory.Published.GrothendieckDeformation) (hQ : GlobalTheory.HSCore.Quoted)
    (hS : GlobalTheory.Published.SiegelToroidalIntegral) (hT : GlobalTheory.Published.ToroidalChartsForFan)
    (hN : GlobalTheory.Published.SemiAbelianLieSeminegative) {D : D7}
    {T : Core D} {j : ℕ} (Y : Deep T j) {e : ℕ} {o : ℝ} (hY : Y.Good e o) (hf : 2 < Module.finrank ℚ D.host.E / 2)
    (hD : 1 ≤ FlagTan.dimFlag (T.Q.Dw j)) (Z : Comp Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (T.Q.Dw j))
    (hla : GapGe (((FlagTan.dimFlag (T.Q.Dw j) + 1).choose 2 + 1 : ℕ) : ℤ) (la - FlagTan.kap (T.Q.Dw j))) :
    ∃ f ∈ cuspOn Y.U Z (wtOf (T.Q.Dw j) la 0), f ≠ 0 := by
  have hP1 := _root_.GlobalTheory.T.covering_topology_refinement hP
  obtain ⟨TF⟩ := _root_.GlobalTheory.T.torFlag_nonempty_of_one_le_dimFlag hP1 _ _ _ _ Y.d.Xo₂ Y.d.c₂ hD
  have hfree := _root_.GlobalTheory.T.hodge_bundle_base_point_free_on_open hP1 hG hQ hP.q15 hP.q16 hS hT hN _ _ _ _ _ _ TF Z _ Y.U hY.geo hD _ hla
    ⟨_root_.GlobalTheory.CompHS.cusp_extends_comp _ _ _ Y _ _ hY hf Z TF _, vanBd_le_space _ _ _ Y _ _ hY hf Z TF _⟩
  haveI := (_root_.GlobalTheory.VarFlag.isVariety₀_flag _ _ _ _ _ _ TF Z hY.geo).2.2
  haveI : ConnectedSpace (Y₀ TF.X Z) := GeometricallyConnected.connectedSpace_of_subsingleton (str₀ TF.X Z)
  obtain ⟨s, hs, hs0⟩ := ne_zero_of_noBase hfree (dense_U₀ TF.X Z).nonempty
  refine ⟨(ofSpace TF.X Z Y.U _ ⟨s, hs⟩).1, (ofSpace TF.X Z Y.U _ ⟨s, hs⟩).2, fun h0 => hs0 ?_⟩
  have h1 : ofSpace TF.X Z Y.U _ ⟨s, hs⟩ = 0 := Subtype.ext h0
  exact congrArg Subtype.val (ofSpace_injective TF.X Z Y.U _ (h1.trans (map_zero _).symm))
end GlobalTheory.CovTop.LowNonzero
end
end

