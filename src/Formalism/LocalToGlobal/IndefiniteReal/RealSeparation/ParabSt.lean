import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def desc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (f : WO S T → ℂ) : WO S T0 → ℂ :=
  fun x0 => Red ψ S T C μ 𝓕 f (embI S T B0 x0)

def hv (T : HSp D) (x y : Fin T.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (x i) * incA D (T.gram i j) * y j

end Formalism.IndefR.Mi

end
