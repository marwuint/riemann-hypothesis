import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LinMulti

noncomputable section

open MeasureTheory Matrix Formalism.MainNotions.S GlobalTheory.Ell
open scoped InnerProductSpace

namespace GlobalTheory.ConjTypeW

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]

def cc (a : V) : EuclideanSpace ℂ (Fin (Module.finrank ℂ V)) :=
  WithLp.toLp 2 fun i => star ((stdOrthonormalBasis ℂ V).repr a i)

theorem cc_apply (a : V) (i) : cc a i = star ((stdOrthonormalBasis ℂ V).repr a i) := rfl

variable {k : ℕ}

theorem lowK_allPos (lam : Fin k → ℝ) (a : Fin k) :
    Formalism.QuantumDeterminants.lowK (allPos k) lam a = lam a - (((k : ℝ) - 1) / 2 - (a : ℕ)) := by
  have h1 : (Finset.univ.filter fun b : Fin k => a < b) = Finset.Ioi a := by ext b; simp
  have h2 : (Finset.univ.filter fun b : Fin k => b < a) = Finset.Iio a := by ext b; simp
  have h3 : (a : ℕ) + 1 ≤ k := a.2
  simp only [allPos, Formalism.QuantumDeterminants.lowK, Formalism.REAL.rhoN, Formalism.REAL.rhoC, Pi.sub_apply, Pi.add_apply, ne_eq, not_true_eq_false,
    and_false, and_true, Finset.filter_false, Finset.card_empty, h1, h2, Fin.card_Ioi, Fin.card_Iio]
  rw [show k - 1 - (a : ℕ) = k - ((a : ℕ) + 1) by omega, Nat.cast_sub h3]
  push_cast; ring

theorem lowK_neg_rev (u : Fin k → ℝ) :
    Formalism.QuantumDeterminants.lowK (allPos k) (fun i => -u (Fin.rev i)) = fun a => -Formalism.QuantumDeterminants.lowK (allPos k) u (Fin.rev a) := by
  funext a
  rw [lowK_allPos, lowK_allPos, Fin.val_rev, Nat.cast_sub a.2]
  push_cast
  ring

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

end GlobalTheory.ConjTypeW

namespace GlobalTheory.ConjTypeW

end GlobalTheory.ConjTypeW
