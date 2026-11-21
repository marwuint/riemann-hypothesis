import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsMetricFrOfIsMetricOn
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ChernDegreeComplex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarOperatorLocalCalculusComplexForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarChernTransgressionFormEqPowerSumDiffStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionSmoothDbarClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramConnectionPairChernFieldsLocalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CurvaturePowerSumTransgressionIsForm

open CategoryTheory AlgebraicGeometry MvPolynomial MeasureTheory Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.L2DbarEstimates (V)
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric GlobalTheory.CxForm GlobalTheory.LineForm GlobalTheory.ChernCalc
open scoped Matrix ContDiff ComplexOrder

namespace GlobalTheory.ChernCalc.PowCoh

variable {M : Type} [TopologicalSpace M] {n : ℕ} {A : HolAtlas M n} {r : Type} [Fintype r] [DecidableEq r]
  {G G' : M → M → Matrix r r ℂ}

theorem pair_symm (h : IsGramPair A G G') : IsGramPair A G' G :=
  ⟨fun y => (h.smooth y).symm, fun y => (h.trans y).mono fun _ ⟨T, K, K', hT, hK, hK', e⟩ =>
    ⟨T, K', K, hT, hK', hK, e.mono fun _ hw => hw.symm⟩⟩

theorem smooth_crd (h : IsGramPair A G G') (x : A.Pt) :
    MContDiffAt ∞ (fun u => G x.pt (x.ch.symm u)) x.crd ∧ IsUnit (G x.pt (x.ch.symm x.crd)).det := by
  refine ⟨((h.smooth x.pt).1.2 x.1.1 x.2).self_of_nhds, ?_⟩
  rw [x.ch.left_inv x.2]
  exact (h.smooth x.pt).1.1

theorem dbar_powFld (h : IsGramPair A G G') (k : ℕ) : A.dbar (fld A (powFld A G k)) = 0 := by
  funext x
  have h₁ := smooth_crd h x
  refine ((_root_.GlobalTheory.CxForm.dbarAt_local_calculus n x.crd).1 _ _ ((_root_.GlobalTheory.ChernCalc.loc_fields_near M n A r G G' h x k).mono fun _ hv => hv.1)).trans ?_
  exact (_root_.GlobalTheory.ChernCalc.powAt_transAt_smooth n r _ _ x.crd h₁.1 h₁.2 h₁.1 h₁.2 k).2.1

theorem dbar_transFld (h : IsGramPair A G G') (k : ℕ) :
    fld A (powFld A G k) - fld A (powFld A G' k) = A.dbar (transFld A G G' k) := by
  funext x
  have h₁ := smooth_crd h x
  have h₂ := smooth_crd (pair_symm h) x
  symm
  refine ((_root_.GlobalTheory.CxForm.dbarAt_local_calculus n x.crd).1 _ _ ((_root_.GlobalTheory.ChernCalc.loc_fields_near M n A r G G' h x k).mono fun _ hv => hv.2.2)).trans ?_
  exact GlobalTheory.T.dbar_chernTransgressionForm_eq_power_sum_diff n r _ _ x.crd h₁.1 h₁.2 h₂.1 h₂.2 k

theorem dbarCoh_powFld : ∀ (M : Type) [TopologicalSpace M] (n : ℕ) (A : HolAtlas M n) (r : Type) [Fintype r]
    [DecidableEq r] (G G' : M → M → Matrix r r ℂ), IsGramPair A G G' → ∀ k,
    DbarCoh A (powFld A G k) (powFld A G' k) := fun M _ n A r _ _ G G' h k =>
  ⟨(_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G G' h k).1, (_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G' G (pair_symm h) k).1, dbar_powFld h k,
    dbar_powFld (pair_symm h) k, _, (_root_.GlobalTheory.ChernCalc.PairForm.isForm_pow_trans M n A r G G' h k).2, dbar_transFld h k⟩

end GlobalTheory.ChernCalc.PowCoh
