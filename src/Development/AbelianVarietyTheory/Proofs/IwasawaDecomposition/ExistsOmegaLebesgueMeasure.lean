import Mathlib
import Formalism.LocalRingCardinality.DataCD
import Formalism.SatakeDualWeyl.KpqSubgroupCompact

open Formalism.BasicNotions MeasureTheory Filter Topology Matrix
open scoped ENNReal NNReal

noncomputable section

namespace GlobalTheory.OmegaLebExists

theorem J_conjTranspose (P Q : ℕ) : (Formalism.UG.Jpq P Q)ᴴ = Formalism.UG.Jpq P Q := by
  unfold Formalism.UG.Jpq
  rw [fromBlocks_conjTranspose]
  simp

end GlobalTheory.OmegaLebExists
