import Formalism.HermitianCurvature.BigCellVanishingOfCommute
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RegularisedPairingViaPhase
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HomogeneityNaturalDegree
import Mathlib.Topology.Algebra.MvPolynomial

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Filter Topology

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

section ops

variable {k r : ℕ} {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp]
  [NormedAddCommGroup Wq] [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

theorem gf_cont (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ) : Continuous fun g : B.Mat k r => Gf k r z z' g := by
  obtain ⟨q, _, hq⟩ := P.gram_function_polynomial k r z z'
  have h1 : Continuous fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ) := by
    have e : (fun g : B.Mat k r => ((Gf k r z z' g : ℝ) : ℂ)) =
        fun g => MvPolynomial.eval (Sum.elim (fun x => g x.1 x.2) (fun x => star (g x.1 x.2))) q := funext hq
    rw [e]
    refine (MvPolynomial.continuous_eval q).comp ?_
    refine continuous_pi fun i => ?_
    rcases i with ⟨a, b⟩ | ⟨a, b⟩
    · simp only [Sum.elim_inl]; exact continuous_id.matrix_elem a b
    · simp only [Sum.elim_inr]; exact continuous_star.comp (continuous_id.matrix_elem a b)
  have := Complex.continuous_re.comp h1
  refine this.congr fun g => ?_
  simp

end ops

end Formalism.FourierDecayAlt.P.DifferentialOperatorClasses

namespace Formalism.FourierDecayAlt.P

end Formalism.FourierDecayAlt.P
