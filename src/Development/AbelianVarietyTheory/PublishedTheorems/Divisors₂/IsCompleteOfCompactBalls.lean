import Mathlib
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.GROWCountStatement
import ReciprocityTheory.L2DbarEstimates.LeviForms.LogNormSq
import ReciprocityTheory.L2DbarEstimates.PlurisubharmonicCharts.AApproxF
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.CommFderivApply

namespace GlobalTheory.L2Kaehler

open MeasureTheory Filter Topology ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y
open scoped ContDiff ENNReal Matrix ComplexOrder

noncomputable section

variable {n : ℕ}

def herm (H : Matrix (Fin n) (Fin n) ℂ) (ξ : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H j k * ξ j * (starRingEnd ℂ) (ξ k)).re

def pairBar (v ξ : Fin n → ℂ) : ℂ := ∑ k, v k * (starRingEnd ℂ) (ξ k)

def coNormSq (H : Matrix (Fin n) (Fin n) ℂ) (v : Fin n → ℂ) : ℝ :=
  (∑ j, ∑ k, H⁻¹ j k * v j * (starRingEnd ℂ) (v k)).re

section Atlas

variable {Y : Type*} [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
  [MeasurableSpace Y] [BorelSpace Y] {ι : Type*} {La : Type*} [AddCommGroup La]

def push (A : WeightedAtlas n Y ι La) (i j : ι) (y : Y) (ξ : Fin n → ℂ) : Fin n → ℂ :=
  (fderiv ℂ (A.chart j ∘ (A.chart i).symm) (A.chart i y) (WithLp.toLp 2 ξ)).ofLp

structure IsKaehler (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) :
    Prop where
  smooth : ∀ i j k, ContDiffOn ℝ ∞ (fun v => H i ((A.chart i).symm v) j k) (A.chart i).target
  posDef : ∀ i y, y ∈ (A.chart i).source → (H i y).PosDef
  trans : ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
    herm (H i y) ξ = herm (H j y) (push A i j y ξ)
  closed : ∀ i, ∀ v ∈ (A.chart i).target, ∀ j k l,
    wd n l (fun w => H i ((A.chart i).symm w) j k) v =
      wd n j (fun w => H i ((A.chart i).symm w) l k) v

def IsC1Path (A : WeightedAtlas n Y ι La) (γ : ℝ → Y) : Prop :=
  ContinuousOn γ (Set.Icc 0 1) ∧
    ∀ i, ContDiffOn ℝ 1 (A.chart i ∘ γ) (Set.Icc 0 1 ∩ γ ⁻¹' (A.chart i).source)

def pathLength (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (γ : ℝ → Y) : ℝ≥0∞ :=
  ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Real.sqrt
    (herm (H (A.pick (γ t)) (γ t)) (deriv (A.chart (A.pick (γ t)) ∘ γ) t).ofLp))

def lengthDist (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (x y : Y) : ℝ≥0∞ :=
  ⨅ (γ : ℝ → Y) (_ : IsC1Path A γ) (_ : γ 0 = x) (_ : γ 1 = y), pathLength A H γ

def IsCauchySeq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (u : ℕ → Y) : Prop :=
  ∀ ε : ℝ≥0∞, 0 < ε → ∃ N, ∀ m ≥ N, ∀ k ≥ N, lengthDist A H (u m) (u k) < ε

def IsComplete (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) : Prop :=
  ∀ u : ℕ → Y, IsCauchySeq A H u → ∃ x, MapClusterPt x atTop u

def IsForm (A : WeightedAtlas n Y ι La) (la : La) (v : ι → Y → Fin n → ℂ) : Prop :=
  (∀ i k, ContDiffOn ℝ ∞ (fun w => v i ((A.chart i).symm w) k) (A.chart i).target) ∧
    ∀ i j y, y ∈ (A.chart i).source → y ∈ (A.chart j).source → ∀ ξ,
      pairBar (v i y) ξ = A.g (A.kap + la) i j y * pairBar (v j y) (push A i j y ξ)

def IsDbarClosed (A : WeightedAtlas n Y ι La) (v : ι → Y → Fin n → ℂ) : Prop :=
  ∀ i, ∀ w ∈ (A.chart i).target, ∀ k l,
    wdb n l (fun x => v i ((A.chart i).symm x) k) w = wdb n k (fun x => v i ((A.chart i).symm x) l) w

def dbar (A : WeightedAtlas n Y ι La) (u : ι → Y → ℂ) : ι → Y → Fin n → ℂ :=
  fun i y k => wdb n k (u i ∘ (A.chart i).symm) (A.chart i y)

def formNsq (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ) (la : La)
    (v : ι → Y → Fin n → ℂ) (y : Y) : ℝ :=
  coNormSq (H (A.pick y) y) (v (A.pick y) y) * Real.exp (-A.ph (A.kap + la) (A.pick y) y)

end Atlas

end

end GlobalTheory.L2Kaehler

namespace GlobalTheory.Published

open MeasureTheory ReciprocityTheory.L2DbarEstimates ReciprocityTheory.L2DbarEstimates.Y GlobalTheory.L2Kaehler
open scoped ENNReal

def DbarCompleteKaehler : Prop :=
  ∀ (n : ℕ) (Y : Type) [TopologicalSpace Y] [T2Space Y] [SecondCountableTopology Y]
    [MeasurableSpace Y] [BorelSpace Y] (ι La : Type) [AddCommGroup La]
    (A : WeightedAtlas n Y ι La) (H : ι → Y → Matrix (Fin n) (Fin n) ℂ)
    (la : La) (ps : Y → ℝ) (ε : ℝ) (v : ι → Y → Fin n → ℂ),
    IsKaehler A H → IsComplete A H → A.SmoothFn ps → 0 < ε →
    (∀ i y, y ∈ (A.chart i).source → ∀ ξ : Fin n → ℂ,
      ε * herm (H i y) ξ ≤ A.leviAt i (fun x => A.ph la i x + ps x) y ξ) →
    IsForm A la v → IsDbarClosed A v →
    ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu < ⊤ →
    ∃ u : ι → Y → ℂ, A.IsSSec (A.kap + la) u ∧
      (∀ i y, y ∈ (A.chart i).source → dbar A u i y = v i y) ∧
      ∫⁻ y, ENNReal.ofReal (A.nsq (A.kap + la) u y * Real.exp (-ps y)) ∂A.mu ≤
        ENNReal.ofReal ε⁻¹ *
          ∫⁻ y, ENNReal.ofReal (formNsq A H la v y * Real.exp (-ps y)) ∂A.mu

end GlobalTheory.Published
