import Formalism.LocalToGlobal.IndefiniteReal.RealSeparation.ParabSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def embS (S T : HSp D) {ρ : ℕ} (CS : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS * S.gram).map (incA D))

def embP (S T : HSp D) {ρ : ℕ} (CS' : Matrix (Fin S.rank) (Fin ρ) D.host.E) (M' : Mx D T.rank ρ) : WO S T :=
  HMul.hMul M' ((Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) CS' * S.gram).map (incA D))

def embQ (S T S0 : HSp D) (BS : Matrix (Fin S.rank) (Fin S0.rank) D.host.E) (x : WO S0 T) : WO S T :=
  HMul.hMul x ((S0.gram⁻¹ * Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) BS * S.gram).map (incA D))

end Formalism.IndefR.Mi

end
