import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FactorResIEqResS
open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Pj Formalism.IndefR.Lev GlobalTheory.IndefiniteRowSideFullHecke GlobalTheory.GeoActCompare
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

noncomputable section

namespace GlobalTheory.GeoActCompare.TameAB

variable {D : D7}

abbrev cFin (D : D7) : Af D.host.F ⊗[D.host.F] D.host.E →+* Af D.host.F ⊗[D.host.F] D.host.E :=
  sigR (Af D.host.F) D.sp.cm.sig

theorem cFin_tmul (a : Af D.host.F) (e : D.host.E) :
    cFin D (a ⊗ₜ e) = a ⊗ₜ IsCMField.complexConj D.host.E e := rfl

end GlobalTheory.GeoActCompare.TameAB

end
