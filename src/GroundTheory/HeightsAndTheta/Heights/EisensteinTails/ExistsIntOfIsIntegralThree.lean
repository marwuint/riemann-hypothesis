import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithDegree
import GroundTheory.HeightsAndTheta.Heights.HermitianSum
set_option maxSynthPendingDepth 1

noncomputable section

open Complex NumberField Filter Topology
open UpperHalfPlane hiding I
open NumberField.ComplexEmbedding
open scoped Real nonZeroDivisors

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum

instance neZero_of_prime (d : ℕ) [Fact d.Prime] : NeZero d := ⟨(Fact.out : d.Prime).ne_zero⟩

def chi (d : ℕ) [Fact d.Prime] : DirichletCharacter ℂ d :=
  (quadraticChar (ZMod d)).ringHomComp (Int.castRingHom ℂ)

def Lval (d : ℕ) [Fact d.Prime] (s : ℂ) : ℂ := DirichletCharacter.LFunction (chi d) s

def abelian₂ (d : ℕ) [Fact d.Prime] (s : ℂ) : ℂ :=
  ((d : ℂ) / π) ^ ((s + 1) / 2) * Gamma ((s + 1) / 2) * Lval d s

def sqrtNeg (d : ℕ) : ℂ := I * (Real.sqrt d : ℂ)

def Kfield (d : ℕ) : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {sqrtNeg d}

abbrev K (d : ℕ) : Type := ↥(Kfield d)

theorem sqrtNeg_sq (d : ℕ) : sqrtNeg d ^ 2 = -(d : ℂ) := by
  rw [sqrtNeg, mul_pow, I_sq, ← ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg d)]
  push_cast
  ring

theorem isIntegral_sqrtNeg (d : ℕ) : IsIntegral ℚ (sqrtNeg d) := by
  refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
  simp [Polynomial.eval₂_add, Polynomial.eval₂_X_pow, sqrtNeg_sq]

instance (d : ℕ) : NumberField (K d) where
  to_finiteDimensional := IntermediateField.adjoin.finiteDimensional (isIntegral_sqrtNeg d)

def expTwoPiI (x : ℝ) : ℂ := cexp (2 * π * I * x)

def rowSum (m : ℤ) (τ : ℍ) (s : ℂ) : ℂ :=
  ∑' n : ℤ, ((‖(m : ℂ) * (τ : ℂ) + n‖ : ℝ) : ℂ) ^ (-2 * s)

def freqIntegral (k : ℤ) (Y : ℝ) (s : ℂ) : ℂ :=
  ∫ t : ℝ, expTwoPiI (-(k * t)) * ((t ^ 2 + Y ^ 2 : ℝ) : ℂ) ^ (-s)

section Hermitian

@[instance_reducible]
def corePi {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ c, AddCommGroup (V c)] [∀ c, Module ℂ (V c)]
    (h : ∀ c, InnerProductSpace.Core ℂ (V c)) : InnerProductSpace.Core ℂ (∀ c, V c) where
  inner x y := ∑ c, (h c).inner (x c) (y c)
  conj_inner_symm x y := by
    rw [map_sum]
    exact Finset.sum_congr rfl fun c _ ↦ (h c).conj_inner_symm _ _
  re_inner_nonneg x := by
    rw [map_sum]
    exact Finset.sum_nonneg fun c _ ↦ (h c).re_inner_nonneg _
  add_left x y z := by
    simp only [Pi.add_apply, (h _).add_left, Finset.sum_add_distrib]
  smul_left x y r := by
    simp only [Pi.smul_apply, (h _).smul_left, Finset.mul_sum]
  definite x hx := by
    have hre : ∑ c, ((h c).inner (x c) (x c)).re = 0 := by
      rw [← Complex.re_sum]
      exact congrArg Complex.re hx
    funext c
    refine core_eq_zero_of_re (h c) _ ?_
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun c _ ↦ (h c).re_inner_nonneg (x c))).1 hre c
      (Finset.mem_univ c)

theorem corePi_inner {ι : Type*} [Fintype ι] {V : ι → Type*} [∀ c, AddCommGroup (V c)]
    [∀ c, Module ℂ (V c)] (h : ∀ c, InnerProductSpace.Core ℂ (V c)) (x y : ∀ c, V c) :
    (corePi h).inner x y = ∑ c, (h c).inner (x c) (y c) := rfl

variable {K' : Type*} [Field K']

instance projective_pi {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ c, AddCommGroup (E c)] [∀ c, Module R (E c)]
    [∀ c, Module.Projective R (E c)] : Module.Projective R (∀ c, E c) :=
  Module.Projective.of_equiv DFinsupp.linearEquivFunOnFintype

variable [NumberField K']

end Hermitian

section Inhabitants

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

end Inhabitants

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LeavesOrthogonalSum
