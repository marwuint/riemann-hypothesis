import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels

noncomputable section

namespace PI.Dv.Tr

open PI.Dv

variable {K : Type} [Field K] [CharZero K] {G : Type} [Group G] [Fintype G]

abbrev cf (T : GoodSet K G) (s : T.S) : K :=
  ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K)

def phiS (T : GoodSet K G) (s : T.S) : Module.End K (T.W s) →ₗ[K] MonoidAlgebra K G where
  toFun X := ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x
  map_add' X Y := by
    simp only [mul_add, map_add, add_smul, Finset.sum_add_distrib]
  map_smul' r X := by
    simp only [mul_smul_comm, map_smul, smul_eq_mul, RingHom.id_apply, Finset.smul_sum, smul_smul]
    refine Finset.sum_congr rfl fun x _ => ?_
    ring_nf

lemma phiS_apply (T : GoodSet K G) (s : T.S) (X : Module.End K (T.W s)) :
    phiS T s X = ∑ x : G, (cf T s * LinearMap.trace K (T.W s) (T.tau s x⁻¹ * X)) • MonoidAlgebra.of K G x :=
  rfl

end PI.Dv.Tr
