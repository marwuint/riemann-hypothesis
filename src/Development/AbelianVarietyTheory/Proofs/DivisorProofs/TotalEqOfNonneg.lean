import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsFlagModelHermSum
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.EqOfIsometricTrivShift

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace Set Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxPts GlobalTheory.VB GlobalTheory.HermFrame
open scoped ContDiff ComplexOrder

namespace GlobalTheory.CurveDens

variable {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {σ : k →+* ℂ}

def part (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Measure (CxPts p σ) :=
  ChartGlue.glueMeas (fun c : AlgChart p σ 1 => c.e) fun c y => ENNReal.ofReal (ρ c y)

def IsDens (ρ : AlgChart p σ 1 → CxPts p σ → ℝ) : Prop :=
  (∀ (c c' : AlgChart p σ 1) (y : CxPts p σ), y ∈ c.e.source → y ∈ c'.e.source →
    ρ c y = ‖ChartGlue.transDet c.e c'.e y‖ ^ 2 * ρ c' y) ∧
  ∀ c : AlgChart p σ 1, ContinuousOn (fun v => ρ c (c.e.symm v)) c.e.target

variable {ρ ρ' : AlgChart p σ 1 → CxPts p σ → ℝ}

theorem part_congr (h : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ c y = ρ' c y) :
    part ρ = part ρ' := by
  unfold part ChartGlue.glueMeas
  refine iSup_congr fun c => Measure.ext fun A hA => ?_
  rw [ChartGlue.chartMeas_apply _ _ hA, ChartGlue.chartMeas_apply _ _ hA]
  refine setLIntegral_congr_fun (ChartGlue.measurableSet_image _
    (c.e.open_source.measurableSet.inter hA) inter_subset_left) ?_
  rintro _ ⟨y, hy, rfl⟩
  simp only [c.e.left_inv hy.1, h c y hy.1]

theorem IsDens.sub (h : IsDens ρ) (h' : IsDens ρ') : IsDens fun c y => ρ c y - ρ' c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', h'.1 c c' y hy hy', mul_sub],
    fun c => (h.2 c).sub (h'.2 c)⟩

theorem IsDens.mul (h : IsDens ρ) {f : CxPts p σ → ℝ} (hf : Continuous f) :
    IsDens fun c y => f y * ρ c y :=
  ⟨fun c c' y hy hy' => by beta_reduce; rw [h.1 c c' y hy hy', mul_left_comm],
    fun c => (hf.comp_continuousOn c.e.continuousOn_symm).mul (h.2 c)⟩

theorem IsDens.congr (h : IsDens ρ) (e : ∀ c : AlgChart p σ 1, ∀ y ∈ c.e.source, ρ' c y = ρ c y) :
    IsDens ρ' :=
  ⟨fun c c' y hy hy' => by rw [e c y hy, e c' y hy', h.1 c c' y hy hy'],
    fun c => (h.2 c).congr fun v hv => e c _ (c.e.map_target hv)⟩

section BC

variable {S : ShortComplex X.Modules} {r s : ℕ} {h : Met p σ S.X₂ (r + s)} (hS : S.ShortExact)
  (h₁ : IsVB S.X₁ r) (h₃ : IsVB S.X₃ s)

end BC

end GlobalTheory.CurveDens
