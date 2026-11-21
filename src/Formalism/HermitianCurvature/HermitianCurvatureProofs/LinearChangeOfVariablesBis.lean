import Formalism.HermitianCurvature.HermitianCurvatureProofs.MajorantEstimate

open Matrix Formalism.FourierDecayAlt Formalism.QuantumDeterminants MeasureTheory
open scoped ComplexConjugate ENNReal

namespace Formalism.FourierDecayAlt.P

namespace C2x7

variable {k r : ℕ}

lemma one_mem_UW (z : Fin (2 * r + k + 1) → ℂ) : (1 : B.Mat k r) ∈ UWset k r z :=
  ⟨WeylGroupFacts.uh_one, fun a => ⟨by simp, by simp⟩, by simp⟩

lemma N_sub_S {z : Fin (2 * r + k + 1) → ℂ} {n : B.Mat k r} (hn : n ∈ Nset k r) : n ∈ Sset k r z :=
  ⟨1, one_mem_UW z, n, hn, by simp⟩

lemma UW_sub_S {z : Fin (2 * r + k + 1) → ℂ} {h : B.Mat k r} (hh : h ∈ UWset k r z) : h ∈ Sset k r z :=
  ⟨h, hh, 1, WeylGroupFacts.mem_n_one, by simp⟩

end C2x7

open C2x5 C2x6 C2x7

end Formalism.FourierDecayAlt.P
