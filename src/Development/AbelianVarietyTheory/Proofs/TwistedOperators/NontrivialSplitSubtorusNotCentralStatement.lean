import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NontrivialSplitSubtorusNotCentral
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

open GlobalTheory.RegSS
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.nontrivial_split_subtorus_not_central : GlobalTheory.RegSS.UnitaryCommutant → GlobalTheory.RegSS.SubtorusLaurent → GlobalTheory.RegSS.CharacterMonomial → GlobalTheory.RegSS.SubtorusNotCentral := by
  exact @GlobalTheory.RegSS.subtorusNotCentral_of
