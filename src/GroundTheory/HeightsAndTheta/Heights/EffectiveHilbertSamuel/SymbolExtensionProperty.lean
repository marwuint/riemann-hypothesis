import Mathlib
import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialOfFun
import GroundTheory.HeightsAndTheta.Heights.ProjTopology
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.SectionL2NormSq
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS

open MeasureTheory Set
open scoped ENNReal ContDiff LinearAlgebra.Projectivization
open ReciprocityTheory.AnForm (levi)
open ReciprocityTheory.AnForm.M (FinHolAtlas ChartPartition chartIdx)
open GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel.Bergman (HolLineBundle sectionSpace IsWeight IsSemipositive)

noncomputable section

def l2n {m : ℕ} (c : Fin m → ℂ) : ℝ := Real.sqrt (∑ i, ‖c i‖ ^ 2)

def cD (D : ℕ) : ℝ := 2 ^ (D + 1) * Real.pi ^ D / ((D - 1).factorial : ℝ)

def tuples (D a : ℕ) : Finset (Fin D → ℕ) := Finset.Nat.antidiagonalTuple D a

variable {D : ℕ} {X : Type} [TopologicalSpace X] {A : FinHolAtlas D X}

def lbTensor (L₁ L₂ : HolLineBundle A) : HolLineBundle A where
  g j k x := L₁.g j k x * L₂.g j k x
  holo j k := fun i => (L₁.holo j k i).mul (L₂.holo j k i)
  ne_zero j k x hx := mul_ne_zero (L₁.ne_zero j k x hx) (L₂.ne_zero j k x hx)
  cocycle j k l x hx := by
    rw [← L₁.cocycle j k l x hx, ← L₂.cocycle j k l x hx]; ring

def lbPow (L : HolLineBundle A) (m : ℕ) : HolLineBundle A where
  g j k x := L.g j k x ^ m
  holo j k := fun i => (L.holo j k i).pow m
  ne_zero j k x hx := pow_ne_zero m (L.ne_zero j k x hx)
  cocycle j k l x hx := by rw [← mul_pow, L.cocycle j k l x hx]

def twist (L₂ L : HolLineBundle A) (m : ℕ) : HolLineBundle A := lbTensor L₂ (lbPow L m)

def wAdd (ψ φ : Fin A.n → X → ℝ) (m : ℕ) : Fin A.n → X → ℝ := fun j x => ψ j x + m * φ j x

def jacDet (A : FinHolAtlas D X) (j k : Fin A.n) (x : X) : ℂ :=
  LinearMap.det ((fderiv ℂ (A.chart k ∘ (A.chart j).symm) (A.chart j x) :
    (Fin D → ℂ) →L[ℂ] (Fin D → ℂ)) : (Fin D → ℂ) →ₗ[ℂ] (Fin D → ℂ))

def IsTopForm (B : HolLineBundle A) (f : Fin A.n → X → ℂ) : Prop :=
  (∀ j, A.HoloOn (A.chart j).source (f j)) ∧
  (∀ j, ∀ x ∉ (A.chart j).source, f j x = 0) ∧
  ∀ j k, ∀ x ∈ (A.chart j).source ∩ (A.chart k).source, f j x = jacDet A j k x * B.g j k x * f k x

def topForms (B : HolLineBundle A) : Submodule ℂ (Fin A.n → X → ℂ) where
  carrier := {f | IsTopForm B f}
  add_mem' := by
    rintro f h ⟨hf1, hf2, hf3⟩ ⟨hh1, hh2, hh3⟩
    refine ⟨fun j i => (hf1 j i).add (hh1 j i), fun j x hx => ?_, fun j k x hx => ?_⟩
    · simp [hf2 j x hx, hh2 j x hx]
    · simp only [Pi.add_apply, hf3 j k x hx, hh3 j k x hx]; ring
  zero_mem' := ⟨fun _ _ => analyticOnNhd_const, fun _ _ _ => rfl, fun _ _ _ _ => by simp⟩
  smul_mem' := by
    rintro c f ⟨hf1, hf2, hf3⟩
    refine ⟨fun j i => (analyticOnNhd_const (v := c)).mul (hf1 j i), fun j x hx => ?_,
      fun j k x hx => ?_⟩
    · simp [hf2 j x hx]
    · simp only [Pi.smul_apply, smul_eq_mul, hf3 j k x hx]; ring

def secMul (f g : Fin A.n → X → ℂ) : Fin A.n → X → ℂ := fun j x => f j x * g j x

open scoped Classical in

def chartLIntegral (A : FinHolAtlas D X) (ρ : Fin A.n → X → ℝ) : ℝ≥0∞ :=
  if h : Nonempty (ChartPartition A) then
    ∑ j, ∫⁻ y in (A.chart j).target,
      ENNReal.ofReal (h.some.χ j ((A.chart j).symm y) * ρ j ((A.chart j).symm y))
  else ⊤

def topFormWeightedL2 (ψ : Fin A.n → X → ℝ) (f : Fin A.n → X → ℂ) : ℝ≥0∞ :=
  chartLIntegral A (fun j x => 2 ^ D * ‖f j x‖ ^ 2 * Real.exp (-ψ j x))

structure HermSpace (B : Submodule ℂ (Fin A.n → X → ℂ)) where

  n : ℕ

  e : Fin n → Fin A.n → X → ℂ
  mem : ∀ i, e i ∈ B
  indep : LinearIndependent ℂ e

namespace HermSpace

end HermSpace

def fsPhi {B : Submodule ℂ (Fin A.n → X → ℂ)} (H : HermSpace B) (j : Fin A.n) (x : X) : ℝ :=
  Real.log (∑ i, ‖H.e i j x‖ ^ 2)

structure FSData (A : FinHolAtlas D X) (Y : Type) [TopologicalSpace Y] where

  L : HolLineBundle A

  L₂ : HolLineBundle A

  W : HermSpace (sectionSpace L 1)

  W₂ : HermSpace (sectionSpace L₂ 1)
  gen : ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, W.e i j x ≠ 0
  gen₂ : ∀ j, ∀ x ∈ (A.chart j).source, ∃ i, W₂.e i j x ≠ 0
  isWeight : IsWeight L (fsPhi W)
  isWeight₂ : IsWeight L₂ (fsPhi W₂)

  ι : X → Y
  isOpenEmbedding : Topology.IsOpenEmbedding ι
  denseRange : DenseRange ι

  Φ : Y → ℙ ℂ (Fin W.n → ℂ)
  continuous_Φ : Continuous Φ
  Φ_ι : ∀ x, (fun i => W.e i (chartIdx A x) x) ∈ (Φ (ι x)).submodule

namespace FSData

end FSData

structure HSData (A : FinHolAtlas D X) (Y : Type) [TopologicalSpace Y] extends FSData A Y where

  β : ℝ
  one_le_β : 1 ≤ β

  T : ℕ
  le_T : D + 1 ≤ T

  φA : Fin A.n → X → ℝ
  isWeightA : IsWeight (twist L₂ L D) φA
  pshA : IsSemipositive A φA
  boundA : ∀ j, ∀ x ∈ (A.chart j).source,
    Real.exp (-φA j x) ≤ β ^ (D + 1) * Real.exp (-(fsPhi W₂ j x + D * fsPhi W j x))

  V : (j : ℕ) → HermSpace (topForms (twist L₂ L (D + j)))

namespace HSData

end HSData

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.EffectiveHS
