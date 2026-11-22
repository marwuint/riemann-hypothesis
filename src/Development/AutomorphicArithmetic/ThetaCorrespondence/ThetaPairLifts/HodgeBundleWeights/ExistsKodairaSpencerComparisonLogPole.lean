import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsBaseFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTransl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamPairingPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechKodairaSpencerMatrixEqZeroOffConjBlocks
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KodairaSpencerRowOfKodairaSpencerValueHodgeFil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentDerivationAffineChart
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CechDeformationGluingOfLogKodairaSpencer
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ExistsConstantCechKodairaSpencerValue
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerMapCompatibilities

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.LogPole
theorem exists_kodaira_spencer_comparison_log_pole : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := by
  intro PP E _ _ _ H Dw l Xo c TF
  obtain ⟨s, hs0, hcore⟩ := _root_.GlobalTheory.T.cech_kodaira_spencer_class_constant PP
  refine ⟨s, hs0, ?_⟩
  intro U n e v hv D Θ hΘ K _ _ P hU hP y' hU' hy' hev
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, g, hπ, hπ', hi, hpol, hu, hbl, hrow, hA, hgA, hA', hgA', hL⟩ :=
    _root_.GlobalTheory.T.kodaira_spencer_map_compatibilities PP E H Dw l Xo c TF U D.1 K P hU y' hU' hy' hev
  have hC := _root_.GlobalTheory.CechTransport.cech_of_logKS E H Dw l Xo c TF U n e v hv D Θ hΘ K P hU hP y' hU' hy' hev A A' π π' i ub h hπ hπ' hi hu
  have hbal := _root_.GlobalTheory.LogPole.ksMatrix_eq_zero_of_ne_conj E H Dw l Xo c TF U n e v hv D Θ hΘ
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap c.F K).injective
  have hK := hcore K A A' i h g hA hgA hA' hgA' _ hL ψ hpol n (fun a => ub (e.symm a).1 (e.symm a).2)
    (Matrix.of fun a b => ev (frX P ≫ TF.Y.j) U.1 hU (Θ a b)) (fun a => (hbl _ _).1) hC
    (fun b => hb (e.symm b)) (fun b => hbl _ _)
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, ψ, ub, hb, hπ, hπ', hi, hpol, hu, fun σ k => hbl σ k,
    fun τ a => ?_⟩
  exact _root_.GlobalTheory.KSRowsFil.isKSRow_of_isKSValue E H Dw K A A' i h hA ψ ub hb n e _ (s : K) (fun σ k => (hbl σ k).1)
    (fun a b hab => by simp only [Matrix.of_apply, hbal a b hab, map_zero]) hK τ.1 a (hrow τ a)
end GlobalTheory.LogPole
end
end

section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CompHS
open GlobalTheory.FlagMod (ev frX frVec)
open GlobalTheory.FlagTan (psiSet HIx VIx TIx IsDef IsVert KSIso)
open ReciprocityTheory.ChartRestriction.G.PullbackSections (tv)
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)
open GlobalTheory.LogPole
open scoped Classical
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.kodaira_spencer_comparison_along_boundary : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (TF : TorFlag Xo c), ∃ s : ℚ, s ≠ 0 ∧ KSCompare TF s := GlobalTheory.LogPole.exists_kodaira_spencer_comparison_log_pole
end
