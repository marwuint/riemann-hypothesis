import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel

open NumberField TensorProduct MeasureTheory Filter Topology Asymptotics

noncomputable section

section Had

variable {K : Type} [Field K] [NumberField K]

def degN (E : HermitianBundle.{0} K) : ℝ := HermitianBundle.normDegree E ⊤

abbrev rk (E : HermitianBundle.{0} K) : ℕ := Module.finrank (𝓞 K) E.carrier

structure SmallFamily (E : HermitianBundle.{0} K) (lam : (K →+* ℂ) → ℝ) where

  vec : Fin (rk E) → E.carrier

  indep : LinearIndependent (𝓞 K) vec

  norm_le : ∀ (σ : K →+* ℂ) (i : Fin (rk E)), ‖fibreVec E.metric σ (vec i)‖ ≤ lam σ

structure Had.Data (K : Type) [Field K] [NumberField K] where

  source : HermitianBundle.{0} K

  target : HermitianBundle.{0} K

  map : source.carrier →ₗ[𝓞 K] target.carrier
  map_injective : Function.Injective map

  A : (K →+* ℂ) → ℝ
  A_pos : ∀ σ, 0 < A σ

  map_le : ∀ (σ : K →+* ℂ) (x : Fibre σ source.carrier),
    ‖FibreSpace.equiv target.metric σ (LinearMap.lTensor (ComplexAt σ) map x)‖ ≤
      A σ * ‖FibreSpace.equiv source.metric σ x‖

  lam : (K →+* ℂ) → ℝ
  lam_pos : ∀ σ, 0 < lam σ

  family : SmallFamily target lam

end Had

def unitBallVolume (R : ℕ) : ℝ :=
  (volume (Metric.ball (0 : EuclideanSpace ℝ (Fin R)) 1)).toReal

structure EuclidLattice (R : ℕ) where

  carrier : Submodule ℤ (EuclideanSpace ℝ (Fin R))
  [discrete : DiscreteTopology carrier]
  [full : IsZLattice ℝ carrier]

attribute [instance] EuclidLattice.discrete EuclidLattice.full

def EuclidLattice.covol {R : ℕ} (La : EuclidLattice R) : ℝ := ZLattice.covolume La.carrier

def EuclidLattice.count {R : ℕ} (La : EuclidLattice R) (b : ℝ) : ℕ :=
  Nat.card {x : La.carrier // ‖(x : EuclideanSpace ℝ (Fin R))‖ ≤ b}

structure LatticeCount.Data (R : ℕ) where

  lattice : EuclidLattice R

  c : ℝ

  vec : Fin R → lattice.carrier
  indep : LinearIndependent ℤ vec
  norm_le : ∀ i, ‖(vec i : EuclideanSpace ℝ (Fin R))‖ ≤ c

def MinkowskiCount.Statement : Prop :=
  (∀ (R : ℕ) (La : EuclidLattice R) (ρ : ℝ), 0 < ρ →
    Real.log (unitBallVolume R) + R * Real.log ρ - Real.log La.covol ≤
      Real.log (La.count (2 * ρ))) ∧
  (∀ R : ℕ, (2 / Real.sqrt R) ^ R ≤ unitBallVolume R)

structure Packing.Data (V : Type) [NormedAddCommGroup V] [NormedSpace ℝ V] where

  lattice : Submodule ℤ V
  [discrete : DiscreteTopology lattice]
  [finite : Module.Finite ℤ lattice]

  points : Finset V
  mem : ∀ x ∈ points, x ∈ lattice
  norm_le : ∀ x ∈ points, ‖x‖ ≤ 1

  b : ℝ
  b_nonneg : 0 ≤ b
  sep : ∀ x ∈ points, ∀ y ∈ points, x ≠ y → Real.exp (-b) ≤ ‖x - y‖

structure Halving.Data where

  a : ℕ → ℝ
  bounded : ∃ C, ∀ n, |a n| ≤ C
  halve : Tendsto (fun n ↦ a (2 * n) - a n / 2) atTop (𝓝 0)
  step : Tendsto (fun n ↦ a (n + 1) - a n) atTop (𝓝 0)

theorem tendsto_inv_succ : Tendsto (fun n : ℕ ↦ 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

def Halving.Data.inv : Halving.Data where
  a n := 1 / ((n : ℝ) + 1)
  bounded := ⟨1, fun n ↦ by
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]⟩
  halve := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 / ((2 * n : ℕ) + 1 : ℝ)) atTop (𝓝 0) :=
      tendsto_inv_succ.comp (tendsto_id.const_mul_atTop' (by norm_num : 0 < 2))
    have h2 := tendsto_inv_succ.div_const (2 : ℝ)
    simpa using h1.sub h2
  step := by
    have h1 : Tendsto (fun n : ℕ ↦ 1 / (((n + 1 : ℕ) : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_inv_succ.comp (tendsto_add_atTop_nat 1)
    simpa using h1.sub tendsto_inv_succ

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.HilbertSamuel
