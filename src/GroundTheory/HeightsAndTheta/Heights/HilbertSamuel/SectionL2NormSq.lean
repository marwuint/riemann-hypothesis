import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.IsPshLocallyIntegrableStatement
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open MeasureTheory Filter Topology Set
open scoped ContDiff ComplexConjugate
open ReciprocityTheory.AnForm (levi hessC)
open ReciprocityTheory.AnForm.M (FinHolAtlas chartIdx)

noncomputable section

namespace Bergman

variable {D : ℕ} {X : Type*} [TopologicalSpace X]

structure HolLineBundle (A : FinHolAtlas D X) where

  g : Fin A.n → Fin A.n → X → ℂ
  holo : ∀ j k, A.HoloOn ((A.chart j).source ∩ (A.chart k).source) (g j k)
  ne_zero : ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, g j k x ≠ 0
  cocycle : ∀ j k l, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source ∩ (A.chart l).source,
    g j k x * g k l x = g j l x

variable {A : FinHolAtlas D X}

def IsSection (L : HolLineBundle A) (n : ℕ) (f : Fin A.n → X → ℂ) : Prop :=
  (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
  (∀ j, ∀ x ∉ (A.chart j).source, f j x = 0) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = L.g j k x ^ n * f k x

theorem holoOn_zero' (U : Set X) : A.HoloOn U (fun _ => (0 : ℂ)) := fun _ => analyticOnNhd_const

theorem holoOn_add' {U : Set X} {f g : X → ℂ} (hf : A.HoloOn U f) (hg : A.HoloOn U g) :
    A.HoloOn U (f + g) := fun j => (hf j).add (hg j)

theorem holoOn_smul' {U : Set X} (c : ℂ) {f : X → ℂ} (hf : A.HoloOn U f) :
    A.HoloOn U (c • f) := fun j => (analyticOnNhd_const (v := c)).mul (hf j)

def sectionSpace (L : HolLineBundle A) (n : ℕ) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | IsSection L n f}
  add_mem' := by
    rintro f h ⟨hf1, hf2, hf3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun j => holoOn_add' (hf1 j) (hh1 j), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx, hh2 j x hx]
    · simp only [Pi.add_apply, hf3 j k x hx, hh3 j k x hx]; ring
  zero_mem' := ⟨fun j => holoOn_zero' _, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨fun j => holoOn_smul' c (hf1 j), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx]
    · simp only [Pi.smul_apply, smul_eq_mul, hf3 j k x hx]; ring

def IsWeight (L : HolLineBundle A) (φ : Fin A.n → X → ℝ) : Prop :=
  (∀ j, A.SmoothOn (A.chart j).source (φ j)) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source,
    φ j x = φ k x + Real.log (‖L.g j k x‖ ^ 2)

def IsSemipositive (A : FinHolAtlas D X) (φ : Fin A.n → X → ℝ) : Prop :=
  ∀ j l, ReciprocityTheory.AnForm.A.IsLeviPsh ((A.chart l).target ∩ (A.chart l).symm ⁻¹' (A.chart j).source)
    (φ j ∘ (A.chart l).symm)

def interp (φ₀ φ₁ : Fin A.n → X → ℝ) (t : ℝ) : Fin A.n → X → ℝ :=
  fun j x => φ₀ j x + t * (φ₁ j x - φ₀ j x)

structure SmoothVolume [MeasurableSpace X] (A : FinHolAtlas D X) where

  μ : Measure X
  isProb : IsProbabilityMeasure μ

  dens : Fin A.n → (Fin D → ℂ) → ℝ
  smooth : ∀ j, ContDiffOn ℝ ∞ (dens j) (A.chart j).target
  pos : ∀ j, ∀ y ∈ (A.chart j).target, 0 < dens j y
  chart_eq : ∀ j, ((volume.restrict (A.chart j).target).withDensity
      fun y => ENNReal.ofReal (dens j y)).map (A.chart j).symm = μ.restrict (A.chart j).source

variable [MeasurableSpace X]

end Bergman

open Bergman

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
