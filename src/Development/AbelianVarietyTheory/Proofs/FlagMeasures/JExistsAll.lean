import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsEquivariantUnitaryCoefficientMapOnto
open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem jExists_all : ∀ (D : D7) (F : ∀ u, Formalism.L2.Forms.Forms0 D u), JExists D F := by
  intro D F X u wt hw
  obtain ⟨J, hJ, -⟩ := _root_.GlobalTheory.St.coefficient_map_exists_onto D X u (F u) wt hw
  exact ⟨J, hJ⟩

end GlobalTheory
