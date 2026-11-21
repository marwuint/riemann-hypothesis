import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.DegreeInhab
import GroundTheory.HeightsAndTheta.Heights.AnalyticLimit.Objects
import GroundTheory.HeightsAndTheta.Heights.Regularisation.PChartLeviThGe
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.AnalyticLimit

open Filter Topology
open scoped ContDiff
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas LocPot IsPotential HoloMap)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular (RegChartData)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Regular.ChartLeviThGe (compat_chart levi_base_indep)

noncomputable section

def C2ConvOn {E : ℕ} {Z : Type} [TopologicalSpace Z] (A : FinHolAtlas E Z) (V : Set Z)
    (g : ℝ → Z → ℝ) (φ : Z → ℝ) : Prop :=
  ∀ (k : Fin A.n) (K : Set (Fin E → ℂ)), IsCompact K →
    K ⊆ (A.chart k).target ∩ (A.chart k).symm ⁻¹' V →
    TendstoUniformlyOn (fun t y => g t ((A.chart k).symm y)) (fun y => φ ((A.chart k).symm y))
        (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K ∧
      TendstoUniformlyOn (fun t y => fderiv ℝ (fderiv ℝ fun y' => g t ((A.chart k).symm y')) y)
        (fun y => fderiv ℝ (fderiv ℝ fun y' => φ ((A.chart k).symm y')) y) (𝓝[>] 0) K

def C2ConvergencePullback.Statement : Prop :=
  ∀ {D E : ℕ} {Y Z : Type} [TopologicalSpace Y] [TopologicalSpace Z] (B : FinHolAtlas D Y)
    (A : FinHolAtlas E Z) (f : Y → Z), HoloMap B A f →
    ∀ (V : Set Z), IsOpen V → ∀ (g : ℝ → Z → ℝ) (φ : Z → ℝ) (φ' : Y → ℝ),
      A.SmoothOn V φ → (∀ y ∈ f ⁻¹' V, φ' y = φ (f y)) →
      (∀ᶠ t in 𝓝[>] (0 : ℝ), A.Smooth (g t)) →
      C2ConvOn A V g φ → C2ConvOn B (f ⁻¹' V) (fun t => g t ∘ f) φ'

end

end GroundTheory.Heights₂.Heights.AnalyticLimit
