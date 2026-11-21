import Mathlib
import Formalism.HermitianLattices.StatementMaj
import Formalism.HermitianLattices.HermitianLatticesProofs.MajLattice

open NumberField
open scoped nonZeroDivisors

noncomputable section

namespace Formalism.HermitianLatticesTheory

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma majDual_realize_apply (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ) (x : V)
    (p : InfinitePlace K × ι × Fin 2) :
    realize b X x p = if p.2.2 = 0 then (fcoord b X p.1 x p.2.1).re
      else (fcoord b X p.1 x p.2.1).im := rfl

lemma majDual_jW_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (w : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) p :
    jW h b X w p = sgnAt h b X p.1 p.2.1 * w p := rfl

end

section
variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

lemma majDual_star_int (r : RingOfIntegers K) : IsIntegral ℤ (star (r : K)) := by
  exact (NumberField.RingOfIntegers.isIntegral_coe r).map (starRingEnd K).toIntAlgHom

end

section
variable {K V ι : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [Fintype ι] [DecidableEq ι]

lemma majDual_mem_zmap {R W : Type*} [Ring R] [Module R V] [AddCommGroup W] (f : V →+ W)
    (M : Submodule R V) (w : W) : w ∈ zmap f M ↔ ∃ y ∈ M, f y = w := by
  exact Iff.rfl

def majDualJ (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) :
    EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) →ₗ[ℝ]
      EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2) where
  toFun := jW h b X
  map_add' := by
    intro u w; ext p; simp only [majDual_jW_apply, PiLp.add_apply]; ring
  map_smul' := by
    intro c u; ext p; simp only [majDual_jW_apply, PiLp.smul_apply, smul_eq_mul,
      RingHom.id_apply]; ring

lemma majDualJ_apply (h : V →ₗ⋆[K] V →ₗ[K] K) (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (u : EuclideanSpace ℝ (InfinitePlace K × ι × Fin 2)) :
    majDualJ h b X u = jW h b X u := rfl

variable [Module (RingOfIntegers K) V] [IsScalarTower (RingOfIntegers K) K V]

end

end Formalism.HermitianLatticesTheory
