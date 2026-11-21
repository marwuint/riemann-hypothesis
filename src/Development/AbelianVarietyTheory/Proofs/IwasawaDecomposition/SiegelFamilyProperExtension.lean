import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSiegPull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrExtensionClosedPoint
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GenericSectionExtendsNormal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsChartOfIsLocalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationTransferModels
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ScaleGenIsGen
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.MoveQkCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.LBLocalC
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LevelMapFiniteEtaleSurjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SysExOfPol
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTamePolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MonomialFormOnChartRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasConesIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialSupportHolds
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsHenselRootResidue
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxPowMaximal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolynomialApproxUniqueness
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HenselRootsCompatible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsDvrLiftFiniteCover
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelObjectClassPrimAndIsoClosed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DegenerationDataNormalRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RigidifiedSymmetricLineBundleGroupPullbackStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrincipalPolarizationOfMumfordBundleSiegelFibre
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniformisationBaseChangeWithCoordinates
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PolarizationLineBundleUnifIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnifPolarizationSquareIso

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.ShFam GlobalTheory.Models GlobalTheory.SiegLoc GlobalTheory.LN GlobalTheory
open scoped CategoryTheory.Obj

noncomputable section

namespace GlobalTheory.SiegLoc.TraitOrd

section Specialise

variable {o : Type} [CommRing o] {ζ : o} {g n : ℕ} {F : SFam g n ζ} {S : Scheme.{0}} {j : F.X ⟶ S} [IsOpenImmersion j]
  {G : Over S} [GrpObj G] {e : F.univ.A.left ⟶ G.left}

theorem isSemiAbelian_of_isGrpPullback {T : Scheme.{0}} {f : T ⟶ S} {G' : Over T} [GrpObj G'] [IsCommMonObj G']
    {π : G'.left ⟶ G.left} (h : IsGrpPullback G' G f π) (hG : IsSemiAbelian G) : IsSemiAbelian G' := by
  obtain ⟨bc, mbc, -⟩ := grpPullback_iso h (isGrpPullback_pullback G f)
  exact isSemiAbelian_of_grpIso bc (IsSemiAbelian.pullback f G hG)

end Specialise

theorem eq_of_associated_pow {V : Type} [CommRing V] [IsDomain V] {ϖ : V} (hϖ : Irreducible ϖ) {a b : ℕ}
    (h : Associated (ϖ ^ a) (ϖ ^ b)) : a = b :=
  le_antisymm ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.dvd) ((pow_dvd_pow_iff hϖ.ne_zero hϖ.not_isUnit).1 h.symm.dvd)

end GlobalTheory.SiegLoc.TraitOrd
