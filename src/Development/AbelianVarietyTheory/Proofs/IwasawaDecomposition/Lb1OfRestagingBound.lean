import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StrictHenselianAcyclic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnlocalizedSaturatedState
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DofOTw
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaPsi
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExportTieMove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMove

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up GlobalTheory.TwistChoice
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 2000000

namespace GlobalTheory.HeightCounting.SerCarry

open GlobalTheory.HeightCounting.SerMove GlobalTheory.Mem.R3.Tr

theorem sideB_facts {D : D7} {cf Rw Pq} {S : RatDat D.ntw} {hL eig θ} (B : SideB D cf Rw (lowAll D) Pq S hL eig θ) {eF}
    (h : eF = B.eF) : HkLaw D S eF hL B.hs B.cHk ∧ LowIn D ∧ PqLaw B.exp Pq := by
  subst h
  refine ⟨B.hkEq, fun i p hp P hP => ?_, B.pq⟩
  rw [B.tw.ringSpec_excludedPlaces_eq i]
  exact Or.inr (B.tw.concreteTwistFrame_extraExcluded_over_smallPrimes i p hp hP)

end GlobalTheory.HeightCounting.SerCarry

end
