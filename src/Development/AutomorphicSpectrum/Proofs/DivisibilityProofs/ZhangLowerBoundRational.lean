import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.ExistsUniqueStatement
import Development.AutomorphicSpectrum.Definitions.DivisibilityTowers.HeckeSectionsIsotropicCommutatorPairingPower
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterNamed
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovGeometry.KleimanNefness.KleimanSt
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelArithIntersectionFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelLogIntegralFormula
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelPointHeightDegree
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelCurveDegreeNef
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RootModelSemipositiveConj
import Development.AutomorphicSpectrum.Proofs.DivisibilityProofs.RationalWeightIntegralCoeffs

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo Filter Topology GlobalTheory.CompanionTheory.Ar.Top

namespace GlobalTheory.CompanionTheory.Ar.Top

theorem zhang_lower_bound_root_model : SuccessiveMinimaLowerBound → ∀ II : IntersectionSystem, IsFullIntersectionSystem II →
    ∀ (Ψ : Type) [Fintype Ψ] (N : ℕ) (M : RootModel Ψ N) (t : ℝ) (lam : Wt Ψ N) (s : ℚ) (e : ℝ), IsRatWt lam →
      M.Semipos t lam s → M.NefFib lam s → (∀ W, M.IsPt W → e ≤ M.ht II t lam s W) →
      ((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N) ≤
        M.arFun II t (linA lam s ^ (dimFl Ψ N + 1)) := by
  intro hZ1 II hII Ψ _ N M t lam s e hrat hsemi hnef hpts
  obtain ⟨q, n, hq, hn⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.clear_rat_weight_coef Ψ N M lam s hrat
  have hp := _root_.GlobalTheory.CompanionTheory.Ar.Top.semipositive_integral_multiple Ψ N M t lam s q n hn hsemi
  have hnf := (_root_.GlobalTheory.CompanionTheory.Ar.Top.nefFib_integral_multiple Ψ N M t lam s q n hn).2 hnef
  have hW : ∀ W, IsArithVar W 1 → M.P ≤ W →
      ((q : ℝ) * e) * degC W ≤ II M.K M.ι W 1 ![combLine (M.line t) n] := by
    intro W h1 h2
    have hpt : M.IsPt W := ⟨h1, h2⟩
    obtain ⟨hd, hI⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Top.ht_combLine_integral_multiple II hII Ψ N M t lam s q n W hn hpt
    rw [hI]
    have hq' : (0 : ℝ) ≤ q := Nat.cast_nonneg q
    have hd' : (0 : ℝ) ≤ degC W := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hpts W hpt) hq') hd'
  have key := hZ1 M.K M.ι M.P M.P (dimFl Ψ N) (combLine (M.line t) n) ((q : ℝ) * e) II hII.1 M.arith le_rfl
    hp.1 hnf hp.2 hW
  have hgeo : geomDeg M.P (combLine (M.line t) n) (dimFl Ψ N) =
      (M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N) := by
    have := _root_.GlobalTheory.CompanionTheory.Ar.Top.geoFun_comb_mixed II hII Ψ N M t (fun _ => lam) (fun _ => (s : ℝ)) q (fun _ => n) (fun _ j => hn j)
    simpa [geomDeg, Finset.prod_const] using this
  rw [hgeo, _root_.GlobalTheory.CompanionTheory.Ar.Top.top_comb_eq_arFun II hII Ψ N M t lam s q n hn] at key
  have hδ : (0 : ℝ) < M.δ := by exact_mod_cast M.δ_pos
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hc : (0 : ℝ) < (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) := by positivity
  refine le_of_mul_le_mul_left ?_ hc
  calc (M.δ : ℝ) * (q : ℝ) ^ (dimFl Ψ N + 1) * (((dimFl Ψ N : ℝ) + 1) * e * M.geoFun (linA lam s ^ dimFl Ψ N))
      = ((dimFl Ψ N + 1 : ℕ) : ℝ) * ((q : ℝ) * e) *
          ((M.δ : ℝ) * (q : ℝ) ^ dimFl Ψ N * M.geoFun (linA lam s ^ dimFl Ψ N)) := by
        push_cast; ring
    _ ≤ _ := key

end GlobalTheory.CompanionTheory.Ar.Top
