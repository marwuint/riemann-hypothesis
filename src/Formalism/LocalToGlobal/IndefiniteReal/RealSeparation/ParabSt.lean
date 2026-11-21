import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.FuncSt

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Eqv MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Mi

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def IsQuotFrame (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) : Prop :=
  IsIsoFrame T C ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C' = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * C = 1 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) C' * T.gram * B0 = 0 ∧
    Formalism.UG.cT (D.sp.cm.sig : D.host.E →+* D.host.E) B0 * T.gram * B0 = T0.gram ∧
    T.rank = 2 * r + T0.rank

def desc (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) {r : ℕ} (C : Matrix (Fin T.rank) (Fin r) D.host.E)
    (μ : Measure (Mx D r S.rank)) (𝓕 : Set (Mx D r S.rank)) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (f : WO S T → ℂ) : WO S T0 → ℂ :=
  fun x0 => Red ψ S T C μ 𝓕 f (embI S T B0 x0)

def IsLeviEmb (T : HSp D) {r : ℕ} (C C' : Matrix (Fin T.rank) (Fin r) D.host.E) (T0 : HSp D)
    (B0 : Matrix (Fin T.rank) (Fin T0.rank) D.host.E) (h0 : GA D T0) (h : GA D T) : Prop :=
  HMul.hMul (mt T h) (C.map (incA D)) = C.map (incA D) ∧
    HMul.hMul (mt T h) (C'.map (incA D)) = C'.map (incA D) ∧
    HMul.hMul (mt T h) (B0.map (incA D)) = HMul.hMul (B0.map (incA D)) (mt T0 h0)

def hv (T : HSp D) (x y : Fin T.rank → AE D) : AE D :=
  ∑ i, ∑ j, cA D (x i) * incA D (T.gram i j) * y j

end Formalism.IndefR.Mi

end
