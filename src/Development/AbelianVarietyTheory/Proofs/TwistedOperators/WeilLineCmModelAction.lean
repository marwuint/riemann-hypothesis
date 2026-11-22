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
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanOneParameterFamilyContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntertwiningSymplecticAndGroupLaw
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousMatrixOneParameterGroupEqExp
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemSymplecticLieAlgebraOfExpSmulMemSymplecticGroStatement
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

namespace GlobalTheory.SchwartzSlope

open Filter Topology
open scoped SchwartzMap RealInnerProductSpace

theorem lintegral_of_integral (l : Type) [Fintype l] (f g : GlobalTheory.RealWeil.Sch l)
    (h : ∫ x, ‖f x‖ ^ 2 = ∫ x, ‖g x‖ ^ 2) : ∫⁻ x, ‖f x‖ₑ ^ 2 = ∫⁻ x, ‖g x‖ₑ ^ 2 := by
  have key : ∀ u : GlobalTheory.RealWeil.Sch l, ∫ x, ‖u x‖ ^ 2 = (∫⁻ x, ‖u x‖ₑ ^ 2).toReal := by
    intro u
    rw [integral_eq_lintegral_of_nonneg_ae (f := fun x => ‖u x‖ ^ 2) (Eventually.of_forall fun x => sq_nonneg ‖u x‖)
      ((by fun_prop : Continuous fun x => ‖u x‖ ^ 2).aestronglyMeasurable)]
    congr 1
    refine lintegral_congr fun x => ?_
    rw [← ofReal_norm_eq_enorm, ENNReal.ofReal_pow (norm_nonneg _)]
  have fin : ∀ u : GlobalTheory.RealWeil.Sch l, ∫⁻ x, ‖u x‖ₑ ^ 2 ≠ ⊤ := by
    intro u
    rw [GlobalTheory.MetaplecticScalarDeriv.lintegral_sq_eq]
    exact ENNReal.pow_ne_top (Lp.eLpNorm_ne_top _)
  rw [key, key] at h
  exact (ENNReal.toReal_eq_toReal_iff' (fin f) (fin g)).1 h

end GlobalTheory.SchwartzSlope

end
