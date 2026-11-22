import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ColNone
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.StepZeroRamifiedFormsTransportIffStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ScalarFormTransportedColumnStepZeroStandard
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BottomSphericalCardWeightIndex

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.L2.Forms MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.LocMod GlobalTheory.MiS GlobalTheory.QPl GlobalTheory.QTw GlobalTheory.AdForm GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Fam GlobalTheory.SeeSaw GlobalTheory.StepData GlobalTheory.SplitWeil
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.Fam.GeoAll.fld GlobalTheory.Fam.GeoAll.val GlobalTheory.Fam.GeoAll.top GlobalTheory.Fam.GeoAll.loc

namespace GlobalTheory.Fam

theorem conv_single_one_of_forall {G : Type} [Monoid G] (l : List (G →₀ ℂ))
    (h : ∀ x ∈ l, x = Finsupp.single 1 1) : GlobalTheory.QPl.conv l = Finsupp.single 1 1 := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have hx : x = Finsupp.single 1 1 := h x (by simp)
    have hl := ih (fun y hy => h y (by simp [hy]))
    show List.foldr _ _ (x :: l) = _
    simp only [List.foldr_cons]
    change (x.sum fun g a => (GlobalTheory.QPl.conv l).sum fun h b => Finsupp.single (g * h) (a * b)) = _
    rw [hx, hl, Finsupp.sum_single_index (by simp), Finsupp.sum_single_index (by simp)]
    simp

end GlobalTheory.Fam
