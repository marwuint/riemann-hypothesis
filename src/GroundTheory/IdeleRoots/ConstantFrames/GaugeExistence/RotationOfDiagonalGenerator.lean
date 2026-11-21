import Mathlib
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GTConnCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.cut_GCore_GenTransferKapCut
import Formalism.HermitianCurvature.HermitianCurvatureProofs.TheSection
import Formalism.HermitianCurvature.FrameExists2
set_option maxSynthPendingDepth 1

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P.CutMP.Gauge Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

namespace GroundTheory.BlockD.FourierDecayAlt.GaugeExists

noncomputable section

def dZv {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] (φ : ℂ → V) (ζ : ℂ) : V :=
  (1 / 2 : ℂ) • (fderiv ℝ φ ζ 1 - Complex.I • fderiv ℝ φ ζ Complex.I)

def QdetSub : Prop :=
  ∀ (A : Type) [Ring A] [Algebra ℂ A] (n : ℕ) (Eo : Fin n → Fin n → A), 1 ≤ n →
    ∃ C : ℕ → A, ∀ u : ℂ, qdet Eo u = algebraMap ℂ A (u ^ n) +
      algebraMap ℂ A (u ^ (n - 1)) * (∑ i, Eo i i - algebraMap ℂ A (((n : ℂ) * ((n : ℂ) - 1)) / 2)) +
      ∑ j ∈ Finset.range (n - 1), algebraMap ℂ A (u ^ j) * C j

end

end GroundTheory.BlockD.FourierDecayAlt.GaugeExists
