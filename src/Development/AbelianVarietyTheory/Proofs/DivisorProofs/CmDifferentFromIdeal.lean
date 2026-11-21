import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointShiftSt
import Development.AbelianVarietyTheory.Definitions.Divisors.HtValOnSubset
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.InjectiveOfSumEq
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieAlgebraEigenDecompositionCMSignature
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.NonemptyPolAVGenericFibreWithLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniqueDifferentialMonHomLieBasis
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.LieLatticeFgAndSpanEqTopRingOfIntegers
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaUniformisationComplexAbelianVariety
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGramMatricesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegreeImagesEigenLinesCmUnitaryShimuraObject
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeDegreeEqSublatticeDegreeAddLogIndex
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCmEllipticCurveWithPeriod
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SemiAbelianHomExtensionDvr
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AbsNormMapRingOfIntegersHomStatement

open AlgebraicGeometry CategoryTheory NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory GlobalTheory.CM GlobalTheory.FlatCM

noncomputable section

namespace GlobalTheory.FlatCore.CMDiff

theorem latRank_iSup {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype ι] (N : ι → Submodule (𝓞 K) V)
    (hi : iSupIndep fun i => Submodule.span K (N i : Set V)) :
    latRank K (⨆ i, N i) = ∑ i, latRank K (N i) := by
  classical
  have hs : Submodule.span K ((⨆ i, N i : Submodule (𝓞 K) V) : Set V) = ⨆ i, Submodule.span K (N i : Set V) := by
    refine le_antisymm (Submodule.span_le.2 ?_) (iSup_le fun i => Submodule.span_mono ?_)
    · have : (⨆ i, N i) ≤ (⨆ i, Submodule.span K (N i : Set V)).restrictScalars (𝓞 K) :=
        iSup_le fun i => fun x hx => (le_iSup (fun i => Submodule.span K (N i : Set V)) i)
          (Submodule.subset_span hx)
      exact this
    · exact SetLike.coe_mono (le_iSup N i)
  unfold latRank
  rw [hs]
  have hinj : Function.Injective (DirectSum.coeLinearMap fun i => Submodule.span K (N i : Set V)) := by
    first
    | exact hi.dfinsupp_lsum_injective
    | exact (iSupIndep_iff_dfinsupp_lsum_injective _).1 hi
    | exact DirectSum.coeLinearMap_injective_of_iSupIndep hi
  rw [← DirectSum.range_coeLinearMap, LinearMap.finrank_range_of_inj hinj, Module.finrank_directSum]

end GlobalTheory.FlatCore.CMDiff

namespace GlobalTheory.FlatCore.CMDiff

end GlobalTheory.FlatCore.CMDiff

end
