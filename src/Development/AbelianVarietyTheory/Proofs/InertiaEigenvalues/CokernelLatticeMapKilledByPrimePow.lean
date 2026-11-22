import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.RepresentationBounds
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinPowKillsLatticeCokernel
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.KillsCokerAllOfKillsCokerPhiModuleLattice
open PowerSeries GlobalTheory.BK

namespace GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow

theorem main : GlobalTheory.IndefiniteRowSideFullHecke.RepresentationBounds.Stmt := by
  intro O K _ _ _ _ _ l e a _ _ _ _ hT ι κ _ _ _ _ Sig U N η H hB D₁ D₂ hD₁ hD₂ F hF
  haveI : FiniteDimensional ℚ_[l] K := hT.finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K
  exact _root_.GlobalTheory.CokerLift.killsAll_of_killsCoker_L O K l e a ι κ η H D₁ D₂ F _
    (_root_.GlobalTheory.CokerL.kills_cokerL O K l e a ι κ η H D₁ D₂ F Sig U N hB hD₁.chars_subset hD₂ hF)

end GlobalTheory.Proof.cokernel_latticeMap_killed_by_prime_pow
