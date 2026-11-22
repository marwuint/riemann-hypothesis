import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.RosatiAdj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.GPowPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.TauBalPow
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LocZeroTranslDiffComp
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsMatrixRingAct
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjMul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxSecPowExt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RosatiAdjPow
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TauBalAdd
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.RosatiAdjointBalancedPowerLift
import Development.AbelianVarietyTheory.Proofs.ThetaFamilyOrigin.RosatiAdjOfPoints
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.PowOActOfGlobalFns
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiInOfComponent
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsCoreOfIsAbelianScheme
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsPolAVGenericFibreOfTriple
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericPointMemModuliOfMeetsAbelianLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecUnitClosedFibre
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPointOfPeriod
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LambdaBundleAdjointOfWeilPairingAdjoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TheoremOfCubePolAbelianScheme
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSecImageNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PrincipalTorusAlgebraic
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsMonHomOfMapLattice
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FamilyUnifOfParts
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsFormEqOne
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ModNOfDvdModulus
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSimTrivialOfMult
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.TypeFnPeriodExistModuliNonempty
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPelUniformisationCompleteDvr

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CechPic GlobalTheory.TripleProd

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.PowBalanceProbe

section Group

variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A]

theorem eq_one_of_cls {L : LB A.left} (hL : L.IsLB) (hK : KTriv A L) {T : Over S} (p : T ⟶ A) (d : Pic T.left)
    (h : pull ((fst T A ≫ p) * snd T A).left (cls L hL) - pull (snd T A).left (cls L hL) =
      pull (fst T A).left d) : p = 1 := by
  refine KerPow.eq_one_of_locGen hK p ((KerPow.locGen_iff _ _ _).1 ?_)
  refine (locZero_iff (fst T A).left (N := Out.translDiff A L p) (LB.isLB_linComb hL _ _)).2 ?_
  rw [cls_translDiff hL, h]
  exact locZero_base _ _

variable {A' : Over S} [GrpObj A'] [IsCommMonObj A']

end Group

variable {R : Type} [CommRing R] [IsDomain R]

end GlobalTheory.PowBalanceProbe
