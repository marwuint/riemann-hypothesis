import Formalism.LocalToGlobal.PairingIndexBounds.OrthogonalChartLevels.FrecAt
import Formalism.LocalToGlobal.InertKernelTheory.FrameInt
import Formalism.LocalToGlobal.GroupLattices.LevelGatherings.PosBridge
import Formalism.LocalRingCardinality.DataKerP

noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.G Formalism.MainNotions.FormalGroupSystem Formalism.L2.G Formalism.L2.G.Cmp Formalism.L2.G.Pend Formalism.MainNotions Formalism.MainNotions.G.CmpJ
open Formalism.L2.Forms Formalism.L2.KerInert.SecondKernelInstances

namespace Formalism.L2.PairingIndexBounds.F

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Gen

variable {p : ℕ} [Fact p.Prime] (X : Sys p) [IsFractionRing X.G.O X.G.Kf] (E : CEmbC X.G) (D : D7)
  (pos : (Σ v : X.Pl, Fin (X.G.P.n' v)) ≃ D.what₂.Tau)

theorem sigD_conj (x : D.host.E) : sigD D (D.host.conj x) = x := by
  have h3 : ∀ y : D.host.E, sigD D y = D.host.conj y := fun y => bridge_star_holds D.R D.host y
  rw [h3, ← Formalism.L2.Herm.star_conj, ← Formalism.L2.Herm.star_conj, star_star]

end Gen

end Formalism.L2.PairingIndexBounds.F

end

