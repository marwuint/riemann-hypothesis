import Mathlib
import Formalism.LocalToGlobal.GlobalTheory.GL5.PNamed
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberFiniteAndGenusMass
import Formalism.LocalToGlobal.GlobalTheory.GL5.PClassDecomp
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GenusMassStdAll
open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.GlobalTheoryTheory.GenusMassVolumes
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem classItemsAt_all : ∀ (D : D7) (n : ℕ), ClassItemsAt D n := fun D n =>
  have h := _root_.GlobalTheory.ClassNumberMass.classFin_and_classMass D
  ⟨genusMassAt_of D (GlobalTheory.genusMassStd_all D) n, classFinAt_of D h.1 n, classMassAt_of D h.2 n⟩

end GlobalTheory
