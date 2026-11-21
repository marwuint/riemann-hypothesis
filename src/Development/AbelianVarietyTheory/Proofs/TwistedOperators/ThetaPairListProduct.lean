import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RealPlaceHeisenbergDerivThetaTransformAlgebraicD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HasDerivAtThetaSumLineFirst
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolynomialDatumActionOfPairStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaPairListAction

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
noncomputable section
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.LineDerivSplit

theorem pure_add₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (f g : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (f + g) φ = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ + GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure g φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, add_mul]

theorem pure_smul₀ {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] (c : ℂ) (f : SInf F κ)
    (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (c • f) φ = c • GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ := by
  funext x
  simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mul_assoc]

theorem pure_listSum {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ] {ι : Type} (l : List ι)
    (h : ι → SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F, (κ → Fv F v) → ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (l.map h).sum φ = (l.map fun i => GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (h i) φ).sum := by
  induction l with
  | nil => funext x; simp [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure]
  | cons a l ih => simp [pure_add₀, ih]

theorem sum_listSum {α ι : Type} [AddCommMonoid α] {m : ℕ} (l : List ι) (a : Fin m → ι → α) :
    ∑ j, (l.map (a j)).sum = (l.map fun i => ∑ j, a j i).sum := by
  induction l with
  | nil => simp
  | cons b l ih => simp [Finset.sum_add_distrib, ih]

end GlobalTheory.LineDerivSplit
