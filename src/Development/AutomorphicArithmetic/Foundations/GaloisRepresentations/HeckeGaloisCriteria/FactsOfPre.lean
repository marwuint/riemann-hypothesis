import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.Tie0CutOfTie0
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.CompatibilityTiesEigenRestriction
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.HeckeGaloisCriteria.ExistsUnitOneAddGenerator
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.AdmissibleJOfRestricted
import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SixthWeightStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MuCharacter
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIrreducibleConstituentsCharpolyProductStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.AbsIrreducibleConstituentRanksUniqueOfCharpoly
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EigencharacterOfSummandCharZero
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ValuationRingModel
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.StringRankOneLengthAndMultisetSumSingleton
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidueCountOfSsRank
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConclusionG6OfAllParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ResidualRankPartExistsOfJointCondition
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CentralElementsFromIdempotentCoeffs

noncomputable section

namespace UpperTheory.GalC

open Formalism Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory Tr

variable {D : D7}

set_option maxHeartbeats 1000000 in

@[reducible] def nchCut (c : CutD D) (x : NChoice D) : NChoice (cut D c) := { x with }

set_option maxHeartbeats 1000000 in
theorem nct_cut (c : CutD D) {x : NChoice D} (h : NChTie D x) : NChTie (cut D c) (nchCut c x) :=
  { h with
    twOf_eq := fun a => h.twOf_eq a.1
    twSide_eq := fun a => h.twSide_eq a.1
    Q_eq := fun a => h.Q_eq a.1
    psi_eq := h.psi_eq.imp fun _ k => ⟨k.1, k.2.1, fun a => k.2.2 a.1⟩ }

end UpperTheory.GalC
