import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FrLink

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.UG NumberField IsDedekindDomain Matrix Formalism.L2.SG.HidaSetting Formalism.L2.SG.ColDict
open Formalism.L2.SG.PoincareInHH.PoincareSetting
open scoped TensorProduct

namespace GlobalTheory.St.G.LinkCheck

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : HidaSetting D) (wt : (VS D).V ≃ₗ[D.host.E] (VS D).V)
  (ιA : X.B.I.E ⊗[X.B.I.F] Af X.B.I.F ≃+* D.host.E ⊗[D.host.F] Ad D.host.F)

theorem embA_rat (hι : GlobalTheory.St.IsAdeleIso X ιA) (x : Fin (D.R.N 0) → D.host.E) :
    embA X wt ιA (fun j => inclE (F := D.host.F) (Ad D.host.F) (x j)) =
      incl X.B.I (X.crd (∑ j, x j • qFr wt j)) := by
  have h1 : ∀ a : D.host.E, ιA.symm (inclE (F := D.host.F) (Ad D.host.F) a) =
      inclE (F := X.B.I.F) (Af X.B.I.F) (X.ιE.symm a) := by
    intro a
    rw [RingEquiv.symm_apply_eq, hι.1, RingEquiv.apply_symm_apply]
  funext i
  simp [embA, qA, incl, HidaSetting.crd, crdOf, h1, Finset.sum_apply]

end GlobalTheory.St.G.LinkCheck

end
