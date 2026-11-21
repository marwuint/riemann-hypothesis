import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.TestVectorMemSchwartzBruhat
import Formalism.SharpRestriction.GlobalSchurBounds.GlobalRankLatticeProofs.UnitTraceSumBounds.LemmaTwoThreeOfSiegelBound
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

namespace Formalism.MainNotions.Ext

open Formalism.BasicNotions Formalism.MainNotions.GL3Theta Formalism.MainNotions.TaylorLogMetric NumberField

variable (D : D7) {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p])

noncomputable def conjK : D.host.K →+* D.host.K :=
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  (AlgEquiv.restrictNormal D.host.conj D.host.K : D.host.K →+* D.host.K)

theorem conjK_coe (x : D.host.K) : ((conjK D x : D.host.K) : D.host.E) = D.host.conj (x : D.host.E) := by
  haveI := Formalism.MainNotions.UnusedSlot33.HK.isGalK D.host
  exact AlgEquiv.restrictNormal_commutes D.host.conj D.host.K x

noncomputable def tauKp : D.host.K →+* ℂ_[p] :=
  lam.comp ((D.host.φ₀.comp (algebraMap D.host.K D.host.E)).codRestrict Qbar.toSubring (fun _ => test_vector_mem_schwartz_bruhat D _))

theorem tauKp_apply (x : D.host.K) : tauKp D lam x = lamC lam (D.host.φ₀ (x : D.host.E)) := by
  unfold tauKp lamC
  first
  | rfl
  | (simp [test_vector_mem_schwartz_bruhat]; done)
  | (rw [dif_pos (test_vector_mem_schwartz_bruhat D _)]; rfl)

end Formalism.MainNotions.Ext
