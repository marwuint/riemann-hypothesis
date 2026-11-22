import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.MirabolicInduction.CfunOmStatements
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.LeavesOrthogonalSum

open Complex UpperHalfPlane NumberField Filter Topology
open scoped MatrixGroups Real

noncomputable section

instance fact_no_root (d : ℕ) [Fact d.Prime] : Fact (∀ r : ℚ, r ^ 2 ≠ -(d : ℚ) + 0 * r) :=
  ⟨fun r h ↦ by
    have hd : (0 : ℚ) < d := by exact_mod_cast (Fact.out : d.Prime).pos
    rw [zero_mul, add_zero] at h
    nlinarith [sq_nonneg r]⟩

abbrev K (d : ℕ) : Type := QuadraticAlgebra ℚ (-(d : ℚ)) 0

instance (d : ℕ) [Fact d.Prime] : NumberField (K d) := {}

def eisTerm (τ : ℍ) (s : ℂ) (p : ℤ × ℤ) : ℂ :=
  ((τ.im : ℂ)) ^ s / ((‖(p.1 : ℂ) * (τ : ℂ) + p.2‖ : ℝ) : ℂ) ^ (2 * s)

def rowSum (m : ℤ) (τ : ℍ) (s : ℂ) : ℂ :=
  ∑' n : ℤ, ((‖(m : ℂ) * (τ : ℂ) + n‖ : ℝ) : ℂ) ^ (-2 * s)

def expTwoPiI (x : ℝ) : ℂ :=
  Complex.exp (2 * π * Complex.I * x)

section Core

variable {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

@[instance_reducible]
def corePi (h : ∀ i, InnerProductSpace.Core ℂ (V i)) : InnerProductSpace.Core ℂ (∀ i, V i) where
  inner x y := ∑ i, (h i).inner (x i) (y i)
  conj_inner_symm x y := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun i _ ↦ (h i).conj_inner_symm (x i) (y i)
  re_inner_nonneg x := by
    rw [map_sum]
    exact Finset.sum_nonneg fun i _ ↦ (h i).re_inner_nonneg (x i)
  add_left x y z := by
    simp only [Pi.add_apply, (h _).add_left, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [Pi.smul_apply, (h _).smul_left, Finset.mul_sum]
  definite x hx := by
    have hx' : ∑ i, (h i).inner (x i) (x i) = 0 := hx
    have hre : ∑ i, RCLike.re ((h i).inner (x i) (x i)) = 0 := by
      rw [← map_sum, hx', map_zero]
    have hz := (Finset.sum_eq_zero_iff_of_nonneg fun i _ ↦ (h i).re_inner_nonneg (x i)).1 hre
    funext i
    exact core_eq_zero_of_re (h i) _ (hz i (Finset.mem_univ i))

end Core

section Bundles

open NumberField.ComplexEmbedding TensorProduct ComplexAt

variable {L : Type*} [Field L]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] (E : ι → Type*) [∀ i, AddCommGroup (E i)]
  [∀ i, Module (𝓞 L) (E i)]

variable {E}

variable [NumberField L] [∀ i, Module.Finite (𝓞 L) (E i)] [∀ i, Module.Projective (𝓞 L) (E i)]

instance : Module.Projective (𝓞 L) (∀ i, E i) :=
  Module.Projective.of_equiv (DFinsupp.linearEquivFunOnFintype (R := 𝓞 L) (M := E))

end Bundles

end

end GroundTheory.Heights₂.Heights.LeavesOrthogonalSum
