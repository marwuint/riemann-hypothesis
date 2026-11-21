import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLabelsSemisimpleParameterGLFiniteField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelsCharOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn

open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_labels_semisimple_parameter_GL_finiteField : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (r : ℕ) (s : SSParam p ℂ r), ∃ (x : Cyc s.1 → Fbar p) (f : (ZMod p)[X]), Labels L s x f := by
  exact @GlobalTheory.ParamLabel.exists_labels
