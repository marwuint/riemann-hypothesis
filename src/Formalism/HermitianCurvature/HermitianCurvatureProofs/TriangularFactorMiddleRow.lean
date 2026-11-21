import Formalism.HermitianCurvature.HermitianCurvatureProofs.DpsiIsDerivation

open Matrix Finset

namespace Formalism.FourierDecayAlt.P.SignAntidiagonal

open Formalism.FourierDecayAlt.C3 Formalism.QuantumDeterminants Formalism.QuantumDeterminants.WeylGroupFacts

noncomputable section

section N1

variable {k r : ℕ}

theorem tau_val (p : Fin (2 * r + k + 1)) :
    (tau k r p).val = if p.val < r ∨ r + k < p.val then 2 * r + k - p.val else p.val := rfl

theorem sgn_one (p : Fin (2 * r + k + 1)) (h : p.val ≠ r + k) : WeylGroupFacts.sgn k r p = 1 := by
  unfold WeylGroupFacts.sgn; rw [if_neg h]

theorem mulVec_hpk (v : Fin (2 * r + k + 1) → ℂ) (l : Fin (2 * r + k + 1)) :
    (Hpk k r *ᵥ v) l = WeylGroupFacts.sgn k r l * v (tau k r l) := by
  simp only [Matrix.mulVec, dotProduct]
  rw [Finset.sum_eq_single (tau k r l)]
  · rw [hpk_row, if_pos rfl]
  · intro m _ hm; rw [hpk_row, if_neg hm, zero_mul]
  · simp

theorem herm_expand (v w : Fin (2 * r + k + 1) → ℂ) :
    herm (Hpk k r) v w = ∑ l, star (w l) * (WeylGroupFacts.sgn k r l * v (tau k r l)) := by
  unfold herm; simp only [dotProduct, mulVec_hpk, Pi.star_apply]

variable (k r) in

def Ym (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) : Matrix (Fin j) (Fin j) ℂ :=
  Matrix.of fun a b => y a (esI k r (Fin.castLE hj b))

end N1

section MajorantSquareBound

variable {k r : ℕ}

theorem esI_val (b : Fin r) : (esI k r b).val = 2 * r + k - b.val := rfl

theorem Ym_apply (j : ℕ) (hj : j ≤ r) (y : Fin j → Fin (2 * r + k + 1) → ℂ) (a c : Fin j) :
    Ym k r j hj y a c = y a (esI k r (Fin.castLE hj c)) := rfl

end MajorantSquareBound

end

end Formalism.FourierDecayAlt.P.SignAntidiagonal
