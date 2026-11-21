import Mathlib
import Development.AbelianVarietyTheory.Statements.FundamentalDomains.ExistsIsAddFundamentalDomain
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.ExistsUniqueEqConstMulOriginSec
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsStandardSmoothOfRelativeDimensionAwayJacobian
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCommGrpObjWeierstrassScheme
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.OpensRangeChartYSupOpensRangeChartZ
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.AddXYZOrChordXYZOrOriginXYZNeZero
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.SurjectiveFst
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.OriginLineBundlePolarisation

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.KeyPow

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve

theorem exists_mem_coordOpen_two {R : Type} [CommRing R] (W : WeierstrassCurve R) (s : Sp R) :
    ∃ x : scheme W, toSpec W x = s ∧ x ∈ coordOpen W 2 := by
  have : Module.Finite (Polynomial R) W.toAffine.CoordinateRing :=
    .of_basis (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine)
  have : FaithfulSMul (Polynomial R) W.toAffine.CoordinateRing :=
    ⟨fun {p q} h => by
      have e := congrArg (fun a => (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine).repr a 0)
        (h (WeierstrassCurve.Affine.CoordinateRing.basis W.toAffine 0))
      simp only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same, smul_eq_mul] at e
      exact (mul_one p).symm.trans (e.trans (mul_one q))⟩
  obtain ⟨y, hy⟩ := Algebra.IsIntegral.comap_surjective (Polynomial R) W.toAffine.CoordinateRing
    (PrimeSpectrum.comap (Polynomial.evalRingHom 0) s)
  refine ⟨chartZ W y, ?_, (opensRange_chartZ W).le ⟨y, rfl⟩⟩
  refine (Scheme.Hom.comp_apply (chartZ W) (toSpec W) y).symm.trans ?_
  rw [chartZ_toSpec]
  change PrimeSpectrum.comap (algebraMap R W.toAffine.CoordinateRing) y = s
  rw [IsScalarTower.algebraMap_eq R (Polynomial R), PrimeSpectrum.comap_comp_apply, hy]
  have e : (Polynomial.evalRingHom (0 : R)).comp (algebraMap R (Polynomial R)) = RingHom.id R := by
    ext; simp
  exact congrArg (fun f => PrimeSpectrum.comap f s) e

end GlobalTheory.KeyPow
