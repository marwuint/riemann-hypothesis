import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KernelsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightsOfSets.Slopes
import GroundTheory.HeightsAndTheta.Heights.ArithDegreeIdeal
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsLines
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLatticeBasis
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexDet
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIsLattice
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesGenIndexTrans
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesIdealLatticeFG
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.PLinesLineDegree
import GroundTheory.PowerSubgroups.CountableNeighbourhoods.CommonDenominator

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels

open NumberField NumberField.ComplexEmbedding TensorProduct Matrix GroundTheory.Heights₂.Heights
open GroundTheory.Heights₂.Heights.ComplexAt
open scoped nonZeroDivisors ComplexOrder

noncomputable section

variable {K : Type} [Field K] [NumberField K]

theorem exists_common_denominator {N : ℕ} {M : Submodule (𝓞 K) (Fin N → K)} (hM : M.FG) :
    ∃ c : 𝓞 K, c ≠ 0 ∧ ∀ v ∈ M, ∀ i, ∃ w : 𝓞 K,
      algebraMap (𝓞 K) K w = algebraMap (𝓞 K) K c * v i :=
  _root_.GroundTheory.Variant₂.N1.exists_common_denominator hM

def intIncl (K : Type) [Field K] (N : ℕ) : (Fin N → 𝓞 K) →ₗ[𝓞 K] (Fin N → K) :=
  LinearMap.compLeft (Algebra.linearMap (𝓞 K) K) (Fin N)

omit [NumberField K] in
theorem intIncl_apply {N : ℕ} (v : Fin N → 𝓞 K) (i : Fin N) : intIncl K N v i = (v i : K) := rfl

omit [NumberField K] in
theorem intIncl_injective (N : ℕ) : Function.Injective (intIncl K N) := fun _ _ h =>
  funext fun i => RingOfIntegers.coe_injective (congrFun h i)

def denom {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] : 𝓞 K :=
  (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose

theorem denom_ne_zero {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    denom M ≠ 0 :=
  (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose_spec.1

theorem denom_mul_mem {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) : denom M • (v : Fin N → K) ∈ LinearMap.range (intIncl K N) := by
  obtain ⟨-, h⟩ := (exists_common_denominator (Module.Finite.iff_fg.mp ‹_›)).choose_spec
  choose w hw using h v v.2
  exact ⟨w, funext fun i => by rw [intIncl_apply, Pi.smul_apply, Algebra.smul_def]; exact hw i⟩

def scaleMap {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    M →ₗ[𝓞 K] (Fin N → 𝓞 K) :=
  (LinearEquiv.ofInjective (intIncl K N) (intIncl_injective N)).symm.toLinearMap ∘ₗ
    (denom M • M.subtype).codRestrict (LinearMap.range (intIncl K N)) (denom_mul_mem M)

theorem intIncl_scaleMap {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) : intIncl K N (scaleMap M v) = denom M • (v : Fin N → K) := by
  simp only [scaleMap, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
  rw [LinearEquiv.ofInjective_symm_apply]
  rfl

theorem scaleMap_apply {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M]
    (v : M) (i : Fin N) : (scaleMap M v i : K) = (denom M : K) * (v : Fin N → K) i := by
  have := congrFun (intIncl_scaleMap M v) i
  rw [intIncl_apply] at this
  rw [this, Pi.smul_apply, Algebra.smul_def]

instance projective_of_finite {N : ℕ} (M : Submodule (𝓞 K) (Fin N → K)) [Module.Finite (𝓞 K) M] :
    Module.Projective (𝓞 K) M :=
  projective_of_isTorsionFree M

@[instance_reducible]
def matrixCore {V : Type*} [AddCommGroup V] [Module ℂ V] {ι : Type*} [Fintype ι]
    (Ψ : V →ₗ[ℂ] (ι → ℂ)) (hΨ : Function.Injective Ψ) (H : Matrix ι ι ℂ) (hH : H.PosDef) :
    InnerProductSpace.Core ℂ V where
  inner x y := star (Ψ x) ⬝ᵥ (H *ᵥ Ψ y)
  conj_inner_symm x y := by
    have hh := hH.1
    simp only [dotProduct, mulVec, Pi.star_apply, map_sum, map_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    have hij : starRingEnd ℂ (H j i) = H i j := by
      simpa using congrFun (congrFun hh i) j
    simp only [RCLike.star_def, Complex.conj_conj, hij]
    ring
  re_inner_nonneg x := by
    have := hH.posSemidef.dotProduct_mulVec_nonneg (Ψ x)
    exact (Complex.nonneg_iff.mp this).1
  add_left x y z := by simp only [map_add, star_add, add_dotProduct]
  smul_left x y r := by simp only [map_smul, star_smul, smul_dotProduct, smul_eq_mul, RCLike.star_def]
  definite x h := by
    by_contra hx
    have hx' : Ψ x ≠ 0 := fun h0 => hx (hΨ (h0.trans (map_zero Ψ).symm))
    exact (hH.dotProduct_mulVec_pos hx').ne' h

instance idealLattice_finite {n : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) :
    Module.Finite (𝓞 K) (idealLattice a) :=
  Module.Finite.iff_fg.mpr (KLinesIdealLatticeFG.fg K a)

def sumBasis {n m k : ℕ} (b : Fin m → Fin n → K) (c : Fin k → Fin n → K)
    (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    Module.Basis (Fin m ⊕ Fin k) K (Fin n → K) :=
  Module.Basis.mk hli (by
    rw [hli.span_eq_top_of_card_eq_finrank' (by simp [hmk])])

def quotLattice {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K) (b : Fin m → Fin n → K)
    (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c)) (hmk : m + k = n) :
    Submodule (𝓞 K) (Fin k → K) :=
  (idealLattice a).map ((coordProj (sumBasis b c hli hmk)).restrictScalars (𝓞 K))

instance quotLattice_finite {n m k : ℕ} (a : Fin n → FractionalIdeal (𝓞 K)⁰ K)
    (b : Fin m → Fin n → K) (c : Fin k → Fin n → K) (hli : LinearIndependent K (Sum.elim b c))
    (hmk : m + k = n) : Module.Finite (𝓞 K) (quotLattice a b c hli hmk) :=
  Module.Finite.iff_fg.mpr ((KLinesIdealLatticeFG.fg K a).map _)

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Kernels
