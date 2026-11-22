import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicIntegersHenselianFiniteResidue

open IsDedekindDomain
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.padicIntegers_henselian_finiteResidue : ∀ (v : HeightOneSpectrum ℤ), HenselianLocalRing (v.adicCompletionIntegers ℚ) ∧ Finite (IsLocalRing.ResidueField (v.adicCompletionIntegers ℚ)) := GlobalTheory.IntAdicHensel.henselianLocalRing_and_finite_residueField
