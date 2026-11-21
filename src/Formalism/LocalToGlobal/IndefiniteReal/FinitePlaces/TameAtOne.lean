import Formalism.LocalToGlobal.IndefiniteReal.DatumVec
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Formalism.LocalToGlobal.IndefiniteReal.WeilFull

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix

namespace Formalism.IndefR.Fin

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def UnrOff (e : AE D) (χ : (AE D)ˣ →* Circle) : Prop :=
  ∀ x : (AE D)ˣ, infPart D (x : AE D) = 1 → finPart D (x : AE D) ∈ intAE D →
    finPart D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ intAE D → (e + cA D e) * (x : AE D) = e + cA D e → χ x = 1

def TameAt (e : AE D) (PP : Formalism.L2.DIV.Pl D.host.E) (χ : (AE D)ˣ →* Circle)
    (c : (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ) : Prop :=
  ∀ (x : (AE D)ˣ) (u : (↥(Formalism.L2.Herm.intAf D.host.F D.host.E))ˣ), (1 - e) * (x : AE D) = 1 - e →
    Datum.toEAf D (x : AE D) = ((u : ↥(Formalism.L2.Herm.intAf D.host.F D.host.E)) : Datum.EAf D) →
    ((χ x : Circle) : ℂ) = ((c (Units.map (Formalism.L2.DIV.resS D.host.F PP).toMonoidHom u) : ℂˣ) : ℂ) ^ k

end Formalism.IndefR.Fin

end
