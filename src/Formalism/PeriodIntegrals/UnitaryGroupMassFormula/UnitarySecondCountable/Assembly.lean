import Mathlib

noncomputable section

namespace PI.UMultOne.UnitaryGroupMassFormula

open Matrix Set

instance unitaryGroup_compactSpace (m : ℕ) : CompactSpace (Matrix.unitaryGroup (Fin m) ℂ) := by
  apply isCompact_iff_compactSpace.mp
  have hK : IsCompact (Set.pi univ fun _ : Fin m => Set.pi univ fun _ : Fin m =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall 0 1
  refine IsCompact.of_isClosed_subset (t := ((Matrix.unitaryGroup (Fin m) ℂ : Submonoid _) :
      Set (Matrix (Fin m) (Fin m) ℂ))) hK isClosed_unitary ?_
  intro U hU
  exact Set.mem_univ_pi.2 fun i => Set.mem_univ_pi.2 fun j =>
    mem_closedBall_zero_iff.2 (entry_norm_bound_of_unitary hU i j)

instance matrix_secondCountable (m : ℕ) : SecondCountableTopology (Matrix (Fin m) (Fin m) ℂ) :=
  inferInstanceAs (SecondCountableTopology (Fin m → Fin m → ℂ))

instance unitaryGroup_secondCountable (m : ℕ) :
    SecondCountableTopology (Matrix.unitaryGroup (Fin m) ℂ) :=
  TopologicalSpace.Subtype.secondCountableTopology _

def tr (m : ℕ) : Matrix.unitaryGroup (Fin m) ℂ → Matrix.unitaryGroup (Fin m) ℂ :=
  Matrix.UnitaryGroup.transpose

end PI.UMultOne.UnitaryGroupMassFormula
