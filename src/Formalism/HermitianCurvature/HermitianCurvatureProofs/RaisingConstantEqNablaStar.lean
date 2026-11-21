import Formalism.HermitianCurvature.StatementM
import Formalism.HermitianCurvature.HermitianCurvatureProofs.MultiplicationOpHom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.LevelNablaStarRelations
import Formalism.HermitianCurvature.HermitianCurvatureProofs.InterlaceSignTwo
import Formalism.HermitianCurvature.HermitianCurvatureProofs.EulerZetaGammaInvIdentity

open Formalism.FourierDecayAlt.M Formalism.FourierDecayAlt Matrix Finset Polynomial

namespace Formalism.FourierDecayAlt.P.Mx5

variable (P : Par)

theorem kap_eq (f : Ty P → ℂ) :
    kap P f = Matrix.diagonal fun π => algebraMap ℂ (Pr P.r) (f π) := rfl

section lead

variable {R : Type*} [Ring R] [Algebra ℂ R]

def Lead (n : ℕ) (c : R) (f : ℂ → R) : Prop :=
  ∃ a : ℕ → R, ∀ Y, f Y = Y ^ n • c + ∑ i ∈ range n, Y ^ i • a i

theorem mon_eval (c : R) (n : ℕ) (Y : ℂ) : c * (algebraMap ℂ R Y) ^ n = Y ^ n • c := by
  rw [← map_pow, ← Algebra.commutes, Algebra.smul_def]

theorem lead_iff (n : ℕ) (c : R) (f : ℂ → R) : Lead n c f ↔
    ∃ p : R[X], p.natDegree ≤ n ∧ p.coeff n = c ∧ ∀ Y, f Y = p.eval (algebraMap ℂ R Y) := by
  constructor
  · rintro ⟨a, ha⟩
    refine ⟨monomial n c + ∑ i ∈ range n, monomial i (a i), ?_, ?_, fun Y => ?_⟩
    · refine (Polynomial.natDegree_add_le _ _).trans (max_le (Polynomial.natDegree_monomial_le _) ?_)
      exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
        (Polynomial.natDegree_monomial_le _).trans (Finset.mem_range.1 hi).le
    · rw [Polynomial.coeff_add, Polynomial.coeff_monomial, if_pos rfl, Polynomial.finset_sum_coeff,
        Finset.sum_eq_zero fun i hi => ?_, add_zero]
      rw [Polynomial.coeff_monomial, if_neg (Finset.mem_range.1 hi).ne]
    · rw [ha, Polynomial.eval_add, Polynomial.eval_monomial, Polynomial.eval_finset_sum, mon_eval]
      simp only [Polynomial.eval_monomial, mon_eval]
  · rintro ⟨p, hp1, hp2, hp3⟩
    refine ⟨fun i => p.coeff i, fun Y => ?_⟩
    rw [hp3, Polynomial.eval_eq_sum_range' (show p.natDegree < n + 1 by omega), Finset.sum_range_succ, hp2,
      mon_eval, add_comm]
    simp only [mon_eval]

variable {n m : ℕ} {c d : R} {f g : ℂ → R}

theorem Lead.mul (hf : Lead n c f) (hg : Lead m d g) : Lead (n + m) (c * d) fun Y => f Y * g Y := by
  rw [lead_iff] at hf hg ⊢
  obtain ⟨p, hp1, hp2, hp3⟩ := hf
  obtain ⟨q, hq1, hq2, hq3⟩ := hg
  refine ⟨p * q, Polynomial.natDegree_mul_le.trans (add_le_add hp1 hq1), ?_, fun Y => ?_⟩
  · rw [Polynomial.coeff_mul_add_eq_of_natDegree_le hp1 hq1, hp2, hq2]
  · rw [hp3, hq3]
    exact (map_mul (Polynomial.eval₂RingHom' (RingHom.id R) (algebraMap ℂ R Y)
      fun a => Algebra.commute_algebraMap_right Y a) p q).symm

end lead

end Formalism.FourierDecayAlt.P.Mx5

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
