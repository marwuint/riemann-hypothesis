import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.Imports
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RelStable
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadSph
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.RadIrr
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerV
import Development.AutomorphicArithmetic.ThetaCorrespondence.HoweDuality.KerVp
import Development.WeilBound.ThetaLifts.SphericalLattices.ExistsFixedSum
import Development.WeilBound.ThetaLifts.SphericalLattices.HoweDuality
import Development.WeilBound.ThetaLifts.SphericalSplitting.SphSplitGeo
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocSubSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HoweDualityForClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaActionExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConstOfPolConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsSubAug
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPairOfIsTriple
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenKerOfContinuous
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareTriple
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.UnifModGrowthOfIsUnifModerate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftPRouteSmall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslatesEqPrimFrameLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoBarZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicHeisenbergActsByLocalSchrodinger
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallySelfDualLatticeIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalAddCharUnramifiedOfSplitsCompletelyAbovePla
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContinuousSingleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PsiUnramifiedAwayDifferent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlaceStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FinPartIdemMulMemIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Definitions.Foundations.NonemptyAlgHomOfNotIsField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicCharacterNontrivialAtPlaces
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerPreservesSchwartzBruhat
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterConductorExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqSmulOfCommuteHeisenbergLinearModelSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquareStanding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VacFn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsComplementaryAdelicSchwartzRestFunction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlCharacterFactorsThroughDetOfTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDiagonalLagrangianInvariantForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzRestrictFinitePlaceMemSchwartzBruh
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicSchwartzSpaceTranslateMemOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProductFunctionOnSumCoordsMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFiniteLengthLeviQuotient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaSubmoduleSupNeTop
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalAtFinitePlaceUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemKAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsBicharPairing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzBruhatMatrixExistsOpenAddSubgroupInvaria
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedScalarIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NormalizedAbsCharacterization
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLinearWittModelLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometryCommutingHeisenbergActsFibrewise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardAdelicAddCharNontrivialFinitePlace
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsLinearOfBilinearSchwartzBruhatProduct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SpanSchwartzBruhatProductEqTop
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ProdFnMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledWeilInertPlaceVacuumEigenfunction
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticFormUnitaryGroupActionInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormEqZeroOfLagrangianAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzAdelicEqSpanPure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFactorPureTensorComponentAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnipotentMapsForThetaTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledVacuumTwistedVacuumConditionDoubledLattic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralPointsIndicatorIsVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPlaceCharacterComponentSmoothUnitaryConductStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open scoped TensorProduct
open scoped Matrix

noncomputable section

namespace UpperTheory.Lit.HoweDuality

open GlobalTheory.HoweGlobalPair

theorem sphTri : PositivityTheory.Sph.SphTri :=
  PositivityTheory.Sph.sphTri_of PositivityTheory.Sph.sphSplit_geo (PositivityTheory.Sph.vacInert PositivityTheory.Sph.howeInert)

theorem locV {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl F) :
    Stable (opFin om v) (relFin om v) ∧
      Rad (opFin om v) (relFin om v) (LinearMap.ker (Rf.p v ∘ₗ (SB (Fin a × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).1
  have hk := kerV hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).1 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem locVp {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {Bs : Base F E} {a a' : ℕ}
    {G : Geo σ a a'} {Xc : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W} {R : RealMaps F a a'} {Rf : FinMaps F a a'}
    (hM : IsMatched Bs G Xc om om' R Rf) (v : Pl F) :
    Stable (opFin om' v) (relFin om' v) ∧
      Rad (opFin om' v) (relFin om' v) (LinearMap.ker (Rf.p' v ∘ₗ (SB (Fin a' × Fin (a + a') → Fv F v)).subtype)) := by
  obtain ⟨ω, ρ, L⟩ := (PositivityTheory.Sph.locRep_tri hM.triple v).2
  have hk := kerVp hM v
  refine ⟨relStable L, ?_⟩
  rcases (sphTri F E σ Bs a a' G Xc om om' hM.triple v).2 with h | h
  · exact radSph L h _ hk.1 hk.2.1 hk.2.2.1
  · exact radIrr L h _ hk.1 hk.2.1 hk.2.2.1

theorem stageVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      ∀ T : Finset (Pl F), Xc.T ⊆ T →
        GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T ≤ N ∨
          ∀ Φ ∈ N, Φ ∈ GlobalTheory.HoweGlobal.algAt G.M' Bs.ψ Bs.emb T → PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN T hT
  classical
  have hTr := hM.triple
  have hg := hTr.geo
  have hc := hTr.chars
  obtain ⟨w₀⟩ := (inferInstance : Nonempty (InfinitePlace F))
  have dV' : G.V'.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 1 (by rw [one_smul]; exact hg.hV'.sig w₀)
  have dW : G.W.J.det ≠ 0 := det_ne_sig_map (Bs.emb w₀).1 Complex.I (hg.hW.sig w₀)
  have hres := resEta_div hc.resα hc.resβ (Nat.add_comm a a')
  have hhk := hecke_div hc.heckeα hc.heckeβ
  have hlie := _root_.GlobalTheory.RealLieFockX.lie_deriv_polX F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  have hcpt := _root_.GlobalTheory.FockCompactX.pol_stable_compact_left F E σ hTr.base.cm a' (a + a') G.V' G.W G.M' Bs.ψ Xc.α (Xc.α / Xc.β) om' hTr.base.std
    hg.hV'.herm dV' hg.hW.skew dW hc.resα hres hc.heckeα hhk hTr.weil' Bs.emb hg.hV'.cartan hg.hW.cartan
  obtain ⟨L, hL, hrange⟩ := GlobalTheory.T.exists_linear_tensor_polyVacuum_pureTensors G.M' Bs.ψ Bs.emb hg.hM'.std T
  have hloc := GlobalTheory.T.howeDuality_realPlaces_polynomialVectors_smallPair F E σ Bs a a' G Xc om om' R Rf hM hreal hlie hcpt
  have hfl := fun v => locVp hM v
  obtain ⟨h1, h2, h3, h4⟩ := _root_.GlobalTheory.HoweGlobalPair.tensor_transfer G.M' Bs.ψ Bs.emb om' (fun v => (hg.hM'.vac v).1) hg.hM'.std N hN T L hL
  have key := tens (ι := T) (M₀ := ↥(G.M'.Pol Bs.ψ Bs.emb))
    (M := fun v : T => ↥(SB (Fin a' × Fin (a + a') → Fv F v.1)))
    (opInf G.M' Bs.ψ Bs.emb om') (fun v => opFin om' v.1)
    (relInf G.M' Bs.ψ Bs.emb om') (fun v => relFin om' v.1)
    (R.p' ∘ₗ (G.M'.Pol Bs.ψ Bs.emb).subtype) (fun v => Rf.p' v.1 ∘ₗ (SB _).subtype)
    hloc.1 (fun v => GlobalTheory.TripleAssembly.rank_SB_adicCompletion_le F _ v.1) hloc.2.1 hloc.2.2.1 hloc.2.2.2.1 hloc.2.2.2.2
    (fun v => (hfl v.1).1) (fun v => (kerVp hM v.1).2.1) (fun v => (hfl v.1).2) (fun v => (kerVp hM v.1).2.2.2)
    (N.comap L) h1 h2 h3 h4
  rcases key with htop | hker
  · left
    intro Φ hΦ
    obtain ⟨t, rfl⟩ := hrange hΦ
    have ht : t ∈ N.comap L := by rw [htop]; exact Submodule.mem_top
    exact ht
  · right
    intro Φ hΦN hΦT
    obtain ⟨t, rfl⟩ := hrange hΦT
    have ht0 := hker (show t ∈ N.comap L from hΦN)
    obtain ⟨m, f, φ, rfl⟩ := GlobalTheory.HoweGlobalPair.decomp t
    refine ⟨T, hT, 0, m, Fin.elim0, Fin.elim0, fun j => ((f j : ↥(G.M'.Pol Bs.ψ Bs.emb)) : SInf F (Fin a' × Fin (a + a'))),
      fun j v => if h : v ∈ T then ((φ j ⟨v, h⟩ : ↥(SB _)) : (Fin a' × Fin (a + a') → Fv F v) → ℂ) else G.M'.vac v,
      fun j => Fin.elim0 j, fun j => ⟨(f j).2, fun v => ?_, fun v hv => by simp only [dif_neg hv]⟩, ?_, ?_, ?_⟩
    · by_cases h : v ∈ T
      · simp only [dif_pos h]; exact (φ j ⟨v, h⟩).2
      · simp only [dif_neg h]; exact (hg.hM'.vac v).1
    · simp
    · rw [map_sum]
      exact Finset.sum_congr rfl fun j _ => hL _ _ _ (fun v h => by simp only [dif_pos h]) (fun v h => by simp only [dif_neg h])
    · rw [LinearMap.mem_ker, map_sum] at ht0
      rw [Fin.sum_univ_zero, ← ht0]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.map_tmul, PiTensorProduct.map_tprod]
      simp

theorem allVp : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E)
    (Bs : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (Xc : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E)
    (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W)
    (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'),
    GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched Bs G Xc om om' R Rf →
    ((∃ L : ℕ, ∀ (m : ℕ) (N : Fin m → Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a')))),
        StrictMono N → (∀ i, GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' (N i)) → m ≤ L) ∧
      ∀ N : Submodule ℂ (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.SInf F (Fin a' × Fin (a + a'))), GlobalTheory.Published.ThetaSubInf G.M' Bs.ψ Bs.emb om' N →
        N ≠ G.M'.Pol Bs.ψ Bs.emb → ∀ f ∈ N, R.p' f = 0) →
    ∀ N : Submodule ℂ ((Fin a' × Fin (a + a') → AF F) → ℂ), GlobalTheory.SquareAgree.IsThetaSubG G.M' Bs.ψ Bs.emb om' N →
      N ≠ GlobalTheory.SquareAgree.algD G.M' Bs.ψ Bs.emb → ∀ Φ ∈ N, PolMatch Bs G Xc R Rf 0 Φ := by
  intro F E _ _ _ _ _ σ Bs a a' G Xc om om' R Rf hM hreal N hN hne Φ hΦ
  by_contra hcon
  obtain ⟨T, hT, hΦT⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb (hN.le hΦ) Xc.T
  apply hne
  refine le_antisymm hN.le fun Ψ hΨ => ?_
  obtain ⟨T', hT', hΨT'⟩ := GlobalTheory.HoweGlobal.exists_algAt G.M' Bs.ψ Bs.emb hΨ T
  rcases stageVp F E σ Bs a a' G Xc om om' R Rf hM hreal N hN T' (hT.trans hT') with h | h
  · exact h hΨT'
  · exact absurd (h Φ hΦ (GlobalTheory.HoweGlobal.algAt_mono G.M' Bs.ψ Bs.emb hT' hΦT)) hcon

end UpperTheory.Lit.HoweDuality

end
