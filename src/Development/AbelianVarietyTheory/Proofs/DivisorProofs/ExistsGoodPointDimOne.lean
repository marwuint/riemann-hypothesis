import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairTAdjTLeft
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilCharSurjectiveAndMapRangeAl
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCobOneOfIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateInclusionRaynaudExtensionAlgebraicPoint
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.LePreimageOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolarizedAbelianCubeFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPolarizationTorsionTower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PDivGroupOmegaFiniteFreeAndPSqMemDlogSpanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTatePairingSandwich
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegrallyClosedInOfIntegers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFreeFiniteBijectiveOfSmooth
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.MulEqZeroOfToCompletion

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct NNReal
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.HTLat GlobalTheory.EigenSplit GlobalTheory.CompHt GlobalTheory.CM GlobalTheory.TorusTateLie
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PointMap

section Good

variable {Λ : Type} [CommRing Λ] [StarRing Λ] {p : ℕ} [Fact p.Prime] {C : Type} [Field C]
  {v : Valuation C ℝ≥0} {O : Type} [CommRing O] [Algebra O C] (hv : v.Integers O) (ε : Eps p C) {R : Type}
  [CommRing R] (j : R →+* O) {B B' B'' : Out.PolAV (Sp R)} (o : B.OAct Λ) (o' : B'.OAct Λ) (o'' : B''.OAct Λ)

theorem homT_act (a : Λ) [IsMonHom (o.act a)] : homT hv ε j o o (o.act a) = (goodPoint hv ε j B o).actT a :=
  LinearMap.ext fun t => Tate.ext fun n => congrArg (t.lev n ≫ ·) (goodPoint_oA hv ε j o a).symm

theorem homT_id : homT hv ε j o o (𝟙 B.A) = LinearMap.id :=
  LinearMap.ext fun t => Tate.ext fun n =>
    (congrArg (t.lev n ≫ ·) ((congrArg _ ((Over.pullback _).map_id _)).trans ((Over.pullback _).map_id _))).trans
      (Category.comp_id _)

variable [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O]

variable [IsAlgClosed C] [CharZero C] [Algebra ℤ_[p] O] [Algebra ℤ_[p] C] [IsScalarTower ℤ_[p] O C]

variable {f : B.A ⟶ B'.A} [IsMonHom f]

end Good

end GlobalTheory.PointMap
