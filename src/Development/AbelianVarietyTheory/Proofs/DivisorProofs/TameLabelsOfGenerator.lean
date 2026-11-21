import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

noncomputable section

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel

namespace GlobalTheory.TameLabel

variable {p : ℕ} [Fact p.Prime]

def teichU (L : GlobalTheory.GLq.LabelDatum p) : (ZMod p)ˣ →* ℂˣ :=
  (L.teich.comp (((algebraMap (ZMod p) (Fbar p)).toMonoidHom).comp (Units.coeHom (ZMod p)))).toHomUnits

theorem teichU_val (L : GlobalTheory.GLq.LabelDatum p) (a : (ZMod p)ˣ) :
    ((teichU L a : ℂˣ) : ℂ) = L.teich (algebraMap (ZMod p) (Fbar p) (a : ZMod p)) := rfl

end GlobalTheory.TameLabel

end
