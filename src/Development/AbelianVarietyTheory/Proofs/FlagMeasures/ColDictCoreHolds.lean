import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LevelMatchIff
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegralFiniteAdeleIsoCommutesWithConjugation
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.TransportRepresentsClassesWeightOne
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIntoStepZeroForms
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryBijectiveOfLevelMatch
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ColumnDictionaryIsometricOfRepresentatives

open MeasureTheory NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.ColDict GlobalTheory.St
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.St

theorem colDictCore_holds : ∀ D : D7, ColDictCore D := by
  intro D
  unfold ColDictCore
  intro X u F Tr hK hLev hStab

  have hConj : ∀ a, Tr.ιA (sigA X.B.I a) = Formalism.UG.sigR (Formalism.L2.Forms.sigD D)
      (FiniteAdeleRing (𝓞 D.host.F) D.host.F) (Tr.ιA a) :=
    GlobalTheory.St.G.IotaSigmaCompatibility.iotaA_sigA D X Tr.ιA ⟨Tr.ιA_rat, Tr.ιA_int⟩
  refine ⟨(_root_.GlobalTheory.ColClass.classes_and_weight D X u F Tr hK hConj hLev).1, _root_.GlobalTheory.St.colDictInto_of_levelMatch D X u F Tr hK hConj hLev,
    _root_.GlobalTheory.St.colDict_bij_of_levelMatch D X u F Tr hK hConj hLev, ?_⟩
  intro what₂ cs hinj hReps
  exact _root_.GlobalTheory.St.colDict_isometric_of_reps D X u F Tr hK hConj hLev hStab what₂ cs hinj hReps

end GlobalTheory.St
