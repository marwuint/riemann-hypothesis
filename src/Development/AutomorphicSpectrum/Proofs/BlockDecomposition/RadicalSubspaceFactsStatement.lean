import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RadicalSubspaceFacts
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.radical_subspace_facts : Radical := by
  exact @GlobalTheory.CompanionTheory.RadicalForm.radical
