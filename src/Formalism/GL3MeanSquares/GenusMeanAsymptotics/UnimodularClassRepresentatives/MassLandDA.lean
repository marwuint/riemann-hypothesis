import Mathlib

open Module Polynomial

noncomputable section

namespace Formalism.HermitianLattices.Ext.L3.QuadAdj

variable {F : Type*} [Field F] (c : F)

theorem monic_pol : (X ^ 2 - C c : F[X]).Monic := monic_X_pow_sub_C c two_ne_zero

theorem natDegree_pol : (X ^ 2 - C c : F[X]).natDegree = 2 := natDegree_X_pow_sub_C

theorem root_mul_root :
    AdjoinRoot.root (X ^ 2 - C c) * AdjoinRoot.root (X ^ 2 - C c) = AdjoinRoot.of (X ^ 2 - C c) c := by
  have h := AdjoinRoot.eval₂_root (X ^ 2 - C c)
  rw [eval₂_sub, eval₂_pow, eval₂_X, eval₂_C] at h
  linear_combination h

theorem rep_eq_zero {a b : F}
    (h : AdjoinRoot.of (X ^ 2 - C c) a + AdjoinRoot.of _ b * AdjoinRoot.root _ = 0) :
    a = 0 ∧ b = 0 := by
  have h1 : AdjoinRoot.mk (X ^ 2 - C c) (C b * X + C a) = 0 := by
    rw [map_add, map_mul, AdjoinRoot.mk_C, AdjoinRoot.mk_C, AdjoinRoot.mk_X, add_comm]
    exact h
  by_contra hne
  have h0 : (C b * X + C a : F[X]) ≠ 0 := by
    intro h0
    apply hne
    have ha := congrArg (fun p => coeff p 0) h0
    have hb := congrArg (fun p => coeff p 1) h0
    simp at ha hb
    exact ⟨ha, hb⟩
  refine AdjoinRoot.mk_ne_zero_of_natDegree_lt (monic_pol c) h0 ?_ h1
  rw [natDegree_pol]
  exact lt_of_le_of_lt natDegree_linear_le one_lt_two

instance finite_adj : Module.Finite F (AdjoinRoot (X ^ 2 - C c)) := (monic_pol c).finite_adjoinRoot

theorem finrank_adj : finrank F (AdjoinRoot (X ^ 2 - C c)) = 2 := by
  rw [(AdjoinRoot.powerBasis' (monic_pol c)).finrank, AdjoinRoot.powerBasis'_dim, natDegree_pol]

section

variable [Fact (Irreducible (X ^ 2 - C c : F[X]))]

variable [CharZero F]

instance isGalois_adj : IsGalois F (AdjoinRoot (X ^ 2 - C c)) := by
  have : Algebra.IsQuadraticExtension F (AdjoinRoot (X ^ 2 - C c)) := ⟨finrank_adj c⟩
  infer_instance

end

end Formalism.HermitianLattices.Ext.L3.QuadAdj
