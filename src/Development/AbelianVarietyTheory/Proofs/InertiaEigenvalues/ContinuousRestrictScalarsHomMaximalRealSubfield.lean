import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDual
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasSatakeGLOfIsSatVecGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotSmIndCongr
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalAdjoinRange
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RamificationIdxEqOneOfIsSquare
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIdeleCharLocalFactorization

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.HeightCounting GlobalTheory.Pst
  GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory

open scoped Topology
namespace GlobalTheory

theorem restrictScalarsHom_maximalRealSubfield_continuous :
    ∀ (E Ω : Type) [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω],
    Continuous (AlgEquiv.restrictScalarsHom (maximalRealSubfield E) : G E Ω →* G (maximalRealSubfield E) Ω) := by
  intro E Ω _ _ _ _ _
  set F := maximalRealSubfield E
  apply continuous_of_continuousAt_one
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  let b := Module.finBasis F M
  set t : Set Ω := Set.range (fun i => ((b i : M) : Ω)) with ht_def
  have hMt : M ≤ IntermediateField.adjoin F t := by
    intro m hm
    have h := congrArg (fun y : M => (y : Ω)) (b.sum_repr ⟨m, hm⟩)
    simp only [IntermediateField.coe_sum, IntermediateField.coe_smul] at h
    rw [← h]
    exact sum_mem fun i _ => IntermediateField.smul_mem _
      (IntermediateField.subset_adjoin F t (Set.mem_range_self i))
  have hint : ∀ x ∈ t, IsIntegral E x := by
    rintro x ⟨i, rfl⟩
    have : IsIntegral F (b i) := IsIntegral.of_finite F _
    exact (IsIntegral.map (IsScalarTower.toAlgHom F M Ω) this).tower_top
  haveI : Finite t := Set.finite_range _
  haveI : FiniteDimensional E (IntermediateField.adjoin E t) :=
    IntermediateField.finiteDimensional_adjoin hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  refine ⟨IntermediateField.adjoin E t, inferInstance, fun σ hσ => hMs ?_⟩
  have hH : IntermediateField.adjoin F t ≤ IntermediateField.fixedField
      (Subgroup.map (AlgEquiv.restrictScalarsHom F (A := Ω) (S := E))
        (IntermediateField.adjoin E t).fixingSubgroup) := by
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [SetLike.mem_coe, IntermediateField.mem_fixedField_iff]
    rintro f ⟨τ, hτ, rfl⟩
    exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hτ x
      (IntermediateField.subset_adjoin E _ hx)
  exact IntermediateField.fixingSubgroup_antitone hMt
    ((IntermediateField.le_iff_le _ _).1 hH ⟨σ, hσ, rfl⟩)

end GlobalTheory
