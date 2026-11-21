import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.FormLaws

open CrystallineSemistableComparison.Onto
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.onto_form_laws : CrystallineSemistableComparison.Onto.FormLaws := by
  exact @GlobalTheory.CompanionTheory.OntoForms.formLaws
