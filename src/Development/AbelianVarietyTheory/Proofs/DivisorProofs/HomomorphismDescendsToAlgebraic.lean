import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowEqOneOfSurjective
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivDescendsToNumberField
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MultiplierIffExistsHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDenominatorOfAdelicLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FractionalIdealNormPowSixMulDiscriminantClassInv
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PolCountableAndTangentExt
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPolarisedAbelianSchemeLieBasisInvariants
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsCmCurvesOfWeierstrassCurves
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.IsDiffSumSmulOfIsLieComb
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealMultiplicationUniformization
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAbelianSchemeOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsSymmetricVeryAmple
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverIffIsProperAndExistsIsAmpleLB

open GlobalTheory.LatVal GlobalTheory.LatJet
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.CMVal
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HomDescentQb

theorem exists_holUnif (A : Over (Sp ℂ)) [GrpObj A] (g : ℕ) (hA : IsAbelianScheme A)
    (hg : SmoothOfRelativeDimension g A.hom) : ∃ L : LB A.left, Nonempty (HolUnif A L g) := by
  have := hA.proper
  have := hA.comm
  obtain ⟨H, m, s, hH, hs, -⟩ := GlobalTheory.SymVeryAmple.exists_symmetric_veryAmple ℂ A hA
  have hamp : Out.RelAmple A H :=
    (GlobalTheory.relAmple_iff_isAmpleLB_of_isAffine A hH).2 (GlobalTheory.isAmpleLB_of_veryAmpleBy hs)
  exact ⟨_, GlobalTheory.RealMultChart.exists_holUnif_of_compact A g hg
    (GlobalTheory.RealMultChart.compactSpace_points A H hamp)
    (fun a n hn => GlobalTheory.RealMultChart.exists_pow_eq A hA a n hn)⟩

end GlobalTheory.HomDescentQb
