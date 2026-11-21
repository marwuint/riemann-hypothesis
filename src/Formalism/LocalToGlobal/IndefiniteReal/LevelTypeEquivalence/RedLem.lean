import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.RedTheta
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.CharLem

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory
  IsDedekindDomain NumberField

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

theorem star_eq_sig (e : D.host.E) : star e = D.sp.cm.sig e := rfl

instance borelMx (m n : ℕ) : BorelSpace (Mx D m n) := ⟨rfl⟩

instance tagMx (m n : ℕ) : IsTopologicalAddGroup (Mx D m n) :=
  inferInstanceAs (IsTopologicalAddGroup (Fin m → Fin n → AE D))

instance measAddMx (m n : ℕ) : MeasurableAdd (Mx D m n) :=
  ⟨fun _ => (continuous_const.add continuous_id).measurable, fun _ => (continuous_id.add continuous_const).measurable⟩

theorem countable_ratMx (m n : ℕ) : Countable (ratMx D m n) := by
  haveI : Countable D.host.E :=
    Countable.of_equiv _ (Module.finBasis ℚ D.host.E).equivFun.symm.toEquiv
  haveI : Countable (Matrix (Fin m) (Fin n) D.host.E) :=
    inferInstanceAs (Countable (Fin m → Fin n → D.host.E))
  unfold ratMx
  have hs : Function.Surjective (fun x : Matrix (Fin m) (Fin n) D.host.E =>
      (⟨_, AddMonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ :
        ((incA D).toAddMonoidHom.mapMatrix (m := Fin m) (n := Fin n)).range)) := by
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := AddMonoidHom.mem_range.mp hy
    exact ⟨x, rfl⟩
  exact hs.countable

end Formalism.IndefR.Eqv

end
