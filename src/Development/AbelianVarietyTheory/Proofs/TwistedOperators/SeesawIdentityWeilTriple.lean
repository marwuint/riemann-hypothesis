import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedThetaIntegralValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlacewiseSeesawTripleOverHermitian
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralModerateGrowthOfBoundedKernel
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ExistsNeZeroOfIsMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPlaceSplitsCompletelyNotMemEmbedding
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawDoublingIntegralIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilRepCommuteAtGoodPlacesAlgebraicVectors

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree

noncomputable section

namespace GlobalTheory.RegGood

theorem isTriple_atPlace {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    {σ : E →ₐ[F] E} {B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E} {a a' : ℕ} {G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a'}
    {X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E} {om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W} {om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W}
    (h : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple B G X om om') (v : HeightOneSpectrum (𝓞 F)) (t : E →ₐ[F] Fv F v) (hv : X.Good v) :
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsTriple { B with v₁ := v, τ₁ := t } G X om om' :=
  { h with
    base := { h.base with }
    geo := { h.geo with hV := { h.geo.hV with }, hV' := { h.geo.hV' with }, hW := { h.geo.hW with } }
    chars := { h.chars with good := hv } }

end GlobalTheory.RegGood

end
