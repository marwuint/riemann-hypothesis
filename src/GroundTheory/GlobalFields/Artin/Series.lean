import Mathlib
import GroundTheory.GlobalFields.Artin.MemInvariantsCompSubtypeIff
import GroundTheory.GlobalFields.TateThesis.HeckeLFunction
import GroundTheory.GlobalFields.TateThesis.NonvanishingPrimes
set_option maxSynthPendingDepth 1

noncomputable section

open IsDedekindDomain NumberField Filter Topology ComplexConjugate

namespace GroundTheory.Global

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [IsGalois K L]

section Convergence

omit [IsGalois K L] in
theorem exists_norm_le (f : Gal(L/K) → ℂ) : ∃ C, ∀ g, ‖f g‖ ≤ C := by
  classical
  have := Fintype.ofFinite Gal(L/K)
  exact ⟨∑ g, ‖f g‖, fun g => Finset.single_le_sum (fun x _ => norm_nonneg (f x))
    (Finset.mem_univ g)⟩

end Convergence

end GroundTheory.Global
