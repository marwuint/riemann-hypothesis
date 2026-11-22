import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanLineIntertwinesRealSchrodinger
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepresentationIntegralAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticGroupMatrixOfPreservesPhaseSpace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

namespace GlobalTheory.ArchCont

open scoped SchwartzMap

theorem lintegral_of_integral {l : Type} [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have hi : ∀ u : GlobalTheory.RealWeil.Sch l, MeasureTheory.Integrable (fun x => ‖u x‖ ^ 2) MeasureTheory.volume := fun u =>
    (u.memLp 2 MeasureTheory.volume).integrable_norm_pow two_ne_zero
  have e : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 = ENNReal.ofReal (∫ x, ‖u x‖ ^ 2) := fun u => by
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hi u) (.of_forall fun x => by positivity)]
    congr 1
    funext x
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  rw [e, e, h]

end GlobalTheory.ArchCont

namespace GlobalTheory.ArchCont

end GlobalTheory.ArchCont

