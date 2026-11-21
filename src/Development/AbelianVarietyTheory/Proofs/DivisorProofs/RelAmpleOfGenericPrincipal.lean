import Mathlib
import Development.AbelianVarietyTheory.Definitions.KeyFormula.KeyRootOfKeyFormula
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrincipallyPolarizedCMExtensionDvr
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.CubicalStrOfTrivTheta
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAdditiveSwapOfTrivAxes
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllSixAbelianSchemeLawsHold
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.GenericAmpleDvr

theorem triv_theta {S : Scheme.{0}} [IsLocallyNoetherian S] {A : Over S} [GrpObj A] [IsCommMonObj A]
    (hA : IsAbelianScheme A) {L : LB A.left} (hL : L.IsLB) : AbLaw.Triv (Theta A L) :=
  CubeNoeth.triv_of_faces allSixLaws.1.globalFns hA hL (thφ A (x3 A)) thε
    (fun r i b h => AbLaw.CubeGen.trivAt_of_formal hL r (AbLaw.CubeGen.prod_face r i b h))
    (fun r b h => AbLaw.CubeGen.prod_face r 0 b h)

end GlobalTheory.GenericAmpleDvr
