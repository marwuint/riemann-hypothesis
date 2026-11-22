import Mathlib
import Development.AbelianVarietyTheory.Definitions.UpperBounds.SumNormSqWPos
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.IntegrandAemeasurable
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OntoStatementPfB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.OmFConnPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.ExhaustGPf

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.Up.DivUpPf

noncomputable section

theorem logSum_contDiffAt {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖g k y‖ ^ 2)) z := by
  have h : ContDiffAt ℝ ∞ (fun y => ∑ k, ‖g k y‖ ^ 2) z := by
    simp only [← Complex.normSq_eq_norm_sq]
    exact ContDiffAt.sum fun k _ => HE.normSq_contDiffAt (HE.contDiffAt_of_punct hU (hg k) hz)
  exact h.log (sum_normSq_pos hne).ne'

theorem logSum_levi_nonneg {n N : ℕ} {U : Set (V n)} (hU : IsOpen U) {g : Fin N → V n → ℂ}
    (hg : ∀ k, DifferentiableOn ℂ (g k) U) {z : V n} (hz : z ∈ U) (hne : ∃ k, g k z ≠ 0)
    (ξ : Fin n → ℂ) :
    0 ≤ (leviV n (fun y => ((Real.log (∑ k, ‖g k y‖ ^ 2) : ℝ) : ℂ)) z ξ).re := by
  obtain ⟨k, hk⟩ := hne
  have hne' : (fun i => g i z) ≠ 0 := fun h => hk (congrFun h k)
  have h := leviLogNormSq n N g z ξ
    (fun i => (HE.contDiffAt_of_punct hU (hg i) hz).of_le HE.two_le_inf) hne'
  simp only [← Complex.normSq_eq_norm_sq]
  have e : (fun y => ((Real.log (∑ k, Complex.normSq (g k y)) : ℝ) : ℂ)) =
      fun y => ((Real.log (sqNorm (fun i => g i y)) : ℝ) : ℂ) := rfl
  rw [e, h, Complex.ofReal_re]
  exact div_nonneg (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)
    (Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X : Data E r}

theorem w_diffOn (Xa : ArchInM X) (x0 : Frame X.Ψ r) (k : Fin Xa.N) :
    DifferentiableOn ℂ (fun z => Xa.w k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Xa.w_van k).1.1.1.1

theorem s_diffOn {Xa : ArchInM X} (Fl : FlatM X Xa) (x0 : Frame X.Ψ r) (k : Fin (nd X)) :
    DifferentiableOn ℂ (fun z => Fl.s k (cpt X x0 z)) (OmF X x0) :=
  OntoB.hol_comp X x0 (Fl.s_van k).1.1.1.1

theorem logw_contDiffAt (Xa : ArchInM X) (x0 : Frame X.Ψ r) {z : V (nd X)} (hz : z ∈ OmF X x0) :
    ContDiffAt ℝ ∞ (fun y => Real.log (∑ k, ‖Xa.w k (cpt X x0 y)‖ ^ 2)) z :=
  logSum_contDiffAt (g := fun k y => Xa.w k (cpt X x0 y)) (OntoB.isOpen_OmF X x0)
    (w_diffOn Xa x0) hz (Xa.w_nz _ hz)

end

end GlobalTheory.Up.DivUpPf

namespace GlobalTheory.Up

end GlobalTheory.Up
