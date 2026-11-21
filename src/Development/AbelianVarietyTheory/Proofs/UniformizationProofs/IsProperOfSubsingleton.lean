import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback
import Development.AbelianVarietyTheory.Definitions.Uniformization.ExistsUniqueSamePt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.FinrankFamOfExpBij
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.NonemptyLinearEquivOfRel
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsDegenerationDataUniformisationUnconditiona
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.WCompat
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SplitTorusGenCubical
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.OverHomEqIffForallIsAlgClosedAlgebra
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TopLePtHomPreimageSmoothOpenIff
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.MulLeftCompOfPullbackPointEquivMul
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SABBaseChangeSt
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeAndExtendOfGenericHoms
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsSplitTorusPointsMulEquiv
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsPullbackSectionNonzeroLocus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsSecGeneratesSpecialFibre
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCubicalSymmetricExtension
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SurjectiveAppTopOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsSemiAbelianAndTqOfIsGt

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TateUnif

theorem rank_add_dim {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} (hR : AdmBase R I) {D : DegData R I}
    {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G]
    [IsCommMonObj G] (hG : IsSemiAbelian G) (U : Unif I D A G) :
    Module.finrank ℤ D.toPre.X + D.toPre.P.g = A.g := by
  obtain ⟨hL, hL₂, -⟩ := GlobalTheory.allSixLaws
  have := hG.geomConnected
  have h₁ := GlobalTheory.finrank_fam_of_expBij hL.secBaseChange R I hR D A G U.toUnifPre 2 one_le_two
    (U.expand 2 one_le_two)
  have h₂ := (GlobalTheory.FamDimension.main hL.globalFns hL.cube hL.square hL₂.secTwist R I D (FractionRing R) 2
    one_le_two).2
  exact Nat.pow_right_injective le_rfl (h₂.symm.trans h₁)

end GlobalTheory.TateUnif
