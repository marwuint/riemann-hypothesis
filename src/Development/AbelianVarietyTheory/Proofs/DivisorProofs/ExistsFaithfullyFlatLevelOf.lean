import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HilbertKodairaSpencer
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsFlatUniversalTorsionTuple
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsIdempotentElemRangeSpMapSubset
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.FaithfullyFlatPointsBaseChangeDescent
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsTorsionSectionsOfRoot
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPullbackDegPreStrictLineBundleIso
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRingActionOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSiegelObjectOfDescendedData
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsProjBySmoothIsProperGeometricallyIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.RelAmpleFormBundlePowerOfPosDef
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsGrpPullbackOfLoc
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsRigidTranslatePrincipalPolarisationOrderTw
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveOfLocalBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTangentIffTanS
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsLieEigenbasisOfLocalizationsAtPrime
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.UniversalCharts.ChartLawPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsLieBasisBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushRProdPtsResP
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsAlgHomOfIsBaseChange
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsIsGenOfUniqueFactorizationMonoid
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsUnitSmulEqOfBijectiveToSpanSingleton
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGeneratorsResidueBasis

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.RealMult
attribute [local instance] Over.cartesianMonoidalCategory
set_option autoImplicit false
noncomputable section

namespace GlobalTheory.RealMult.LevFlat

section Alg

variable {M O : Type} [CommGroup M] [CommRing O] (ρ : O → M →* M)

structure IsAct : Prop where
  add : ∀ a b x, ρ (a + b) x = ρ a x * ρ b x
  one : ∀ x, ρ 1 x = x
  mul : ∀ a b x, ρ (a * b) x = ρ b (ρ a x)

variable {ρ}

end Alg

end GlobalTheory.RealMult.LevFlat

namespace GlobalTheory.RealMult

namespace LevFlat

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F}

def ptAct {S : Scheme.{0}} (X : Obj F 𝔠 S) (T : Over S) (a : 𝓞 F) : (T ⟶ X.A) →* (T ⟶ X.A) where
  toFun x := x ≫ X.rm.act a
  map_one' := by
    haveI := X.rm.hom a
    exact MonObj.one_comp _
  map_mul' x y := by
    haveI := X.rm.hom a
    exact MonObj.mul_comp x y _

theorem ptAct_apply {S : Scheme.{0}} (X : Obj F 𝔠 S) (T : Over S) (a : 𝓞 F) (x : T ⟶ X.A) :
    ptAct X T a x = x ≫ X.rm.act a := rfl

end LevFlat

end GlobalTheory.RealMult

namespace GlobalTheory.RealMult.LevFlat

end GlobalTheory.RealMult.LevFlat

namespace GlobalTheory.RealMult

end GlobalTheory.RealMult
