import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisenbergOperatorIsotropicTranslationCharSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun
open scoped Matrix
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open scoped GlobalTheory.VacAny
noncomputable section

namespace GlobalTheory.SwapSchur

open GlobalTheory.SwapSlice

def splitC {R : Type} {m n : ℕ} (Y : Matrix (Fin m) (Fin (n + n)) R) :
    Matrix (Fin m) (Fin n) R × Matrix (Fin m) (Fin n) R :=
  (fun i j => Y i (Fin.castAdd n j), fun i j => Y i (Fin.natAdd n j))

end GlobalTheory.SwapSchur
