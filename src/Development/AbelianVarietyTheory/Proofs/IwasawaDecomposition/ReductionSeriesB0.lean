import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenUsedOfCenReal
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SettingsFormsExistList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCharacterGridData
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsToricCharactersInTwistCoefficientRings
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NoFormsOff
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGlIntertwinerOfResidualSpanEqTop
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.UnramifiedNoJump
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsAuxiliaryHeckeCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RankOneCuspidalUnitaryCharEquivApplySymm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLamTie0OfIsLamTie
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumThEmptyNeZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTwLFull
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExponentAndTwistData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsGaloisRepFamilyBounded
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsAlgWeightFWeightTensorDualRepOfEmbeddings
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorDualRepDualHighestWeightAtEmbedding
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightTensorRepOfEmbeddingsIsIrreducible
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContragredientIsIrreducibleFiniteDimensional
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIrreducibleBaseChangeWeightTensorDualRepOfEmbeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HighestWeightDoubleDualCoefficientSpaceUnique
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CmTypeEmbeddingAtSideDistinctNonconjugate
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CharZeroFractionRingCoefficientRing
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftWeightParamEqInfinitesimalCharacterOfHalfInt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistedLatticeFinitelyGeneratedSpanningStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCentralGroupAlgebraIdempotentUniversal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsSignatureDataSpan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeBasisFreeModulePlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeComparisonUnitAtFrobeniusEqDeltaStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TwistLiftFormsEqBaseChangeRationalDatumForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistIndexOfCoefficientFieldPlace
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GenericUnipotentCharacterAtSideEqThetaSide
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UniversalCharacterAdmissibleConductorInertiaSurjStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasTameBlockCharacterTypePlaceNotOverL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PlacesOverRealSubfieldSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsTwistRingsCharactersClassGroupsStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBasisCoordLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChebSplitNd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormLeOneOfMemClC
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideDataOverSetLevels
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConductorPrimesInLowSet

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up

noncomputable section
namespace GlobalTheory.HeightCounting.Up.PointwiseSettings
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 4000000

theorem exists_Sx (D : D7) : ∃ Sx : Finset (PlE D.host), (∀ p ∈ lowAll D, placesOver D.host.E p ⊆ ↑Sx) ∧
    OverSet D Sx (lowAll D) ∧ (∀ P P', P ∈ Sx → IsConjPl D.host P P' → P' ∈ Sx) := by
  have hne : ∀ p ∈ lowAll D, p ≠ 0 := by
    intro p hp
    simp only [lowAll, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with hp | rfl | rfl | rfl | rfl
    · exact lowPr_ne_zero D p hp
    · exact (D.host.g_prime 0).ne_zero
    · exact (D.host.g_prime 1).ne_zero
    · exact D.host.pde_prime.ne_zero
    · exact D.host.pde'_prime.ne_zero
  have hfin : (⋃ p ∈ (lowAll D : Set ℕ), placesOver D.host.E p).Finite :=
    Set.Finite.biUnion (Finset.finite_toSet _) fun p hp => Formalism.L2.TwC.placesOver_finite' D.host.E p (hne p hp)
  refine ⟨hfin.toFinset, fun p hp Q hQ => ?_, fun Q hQ => ?_, fun Q Q' hQ hc => ?_⟩
  · rw [Set.Finite.coe_toFinset]
    exact Set.mem_biUnion (Finset.mem_coe.2 hp) hQ
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact ⟨p, hp, hQp⟩
  · obtain ⟨p, hp, hQp⟩ := Set.mem_iUnion₂.1 ((Set.Finite.mem_toFinset hfin).1 hQ)
    exact (Set.Finite.mem_toFinset hfin).2 (Set.mem_biUnion hp (placesOver_conj D p hQp hc))

end GlobalTheory.HeightCounting.Up.PointwiseSettings
