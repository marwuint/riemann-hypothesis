import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SeparableIrreducible
import Development.WeilBound.CoreStatements.FiniteTypeHarishChandra.SupportExistsAll
open ReciprocityTheory.Ty.Fin
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.separable_irreducible : ReciprocityTheory.Ty.Fin.St.SepIrr := by
  exact @GlobalTheory.CompanionTheory.FinRep.sepIrr
