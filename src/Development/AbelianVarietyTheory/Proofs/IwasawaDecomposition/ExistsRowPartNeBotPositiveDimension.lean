import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LatticeFramesOfHyps
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.RegularisedSiegelWeilFirstTerm
import Development.AbelianVarietyTheory.Definitions.Divisors.Hypotheses2
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonzeroPlacesOverPrimesLifts
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.WeakCharInertPartRealAdelicDataTransport
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RowEigensystemCarriedByFiniteType
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPartnerCombinationGoodInertLift
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWFormsEqPrincipalForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseLevelWOrthogonalSumOfParts
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeClose
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.InertJunkColIn3
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsRowPartNeBotPositiveDimension
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PosAtBase
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FiniteTypeCarriesOnePart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsUnitaryRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsPart
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodFormsDefiniteExist
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsNilpotentSubOneOfFullBlockUnipotent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HyperspecialFixesVacuaGoodInertPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EOpEqAsAlgebraHom
import Development.AbelianVarietyTheory.PublishedTheorems.SiegelWeil₂.SiegelEisensteinContinuationOfDoublingMethod
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftScalarIdentityMatchingAdjointInjective
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.HeckeFormNSOfHeckeForm
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.PartW
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaInnerProductEqConstMulLValue
import Formalism.UnipotentAdelicQuotients.SiegelWeilUnitaryConvergent
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PrinInf
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsThetaFam
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.SkewGramHalfModule
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HeckeLPartialContinuationHolds
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingSiegelWeilSectionMemDegeneratePrincipalSStatement
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IntegrandSZero
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SiegelWeilSectionDoublingEqMatrixCoefficient
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingMapThetaIdentityAnyWeilDataStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsArchimedeanKFiniteStarCompMem
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BoxProductsOrthogonalSumTargetCartanFock
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingIntegralsVanishOfAllLiftsVanishStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.LevelPlacesIntegralNonzeroConstant
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ZetaResidueNeZeroOfSimplePoleLiftLFunctionStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsInfFamAndStdChar
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.CovolOneIntegralAdd
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDoubledGroupSelfDualLattice
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKillingImpliesVanishing
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaKernelExistsForContinuous
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TameOfHeisDer
import Development.AbelianVarietyTheory.Proofs.HeightProofs.AdelicUnitaryRealPointsStructureRealPlaces
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankOrth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWittDecompositionIsotropicSplitUnipotent
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.EmbRelExistsUnique
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicIwasawaDecompositionWittIsotropicStabilizeStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaMajorantAverageIdentity
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsVacuumVectorPrincipalCongruenceSupport
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSumHyperbolicPlanesOrthogonalWittDecomposi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteRealGroupFixesSplitSpaceWeilVacuum
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DefiniteUnitaryQuotientCompactFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingZetaValueAtEisensteinHolomorphicPoint
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ContAutRapidDecBoundedIntegrable
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsWeilDatumHermitianSpaceDoubled
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsThetaFunctionDoublingSeesawOfStandardChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingVectorFockPairIsCompactFinite
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilDatumAtPlaceEqLatticeIntertwinerMulDetChar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.DoublingEulerProductFarRightOfRapidDecayUnramifi
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftNonvanishingOnStringOfDefiniteDown
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnramifiedThetaCorrespondenceAllGoodPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftEigenformIsEigenformStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationFinitePlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LengthPosOfPosDef
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.GaussianBinomialClosedForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ThetaLiftGenerationAtRealPlaces
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DownwardThetaLiftPreservesGood
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GoodTypesExcludeLevelCharacter
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasStringOfLift
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsParamDefinite
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TypeNZOfNonVanGen
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimplePoleOfHecke
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ParamsEx
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdjFormula
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UpInjWOfAForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoreClausesOfWeakCharacterisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchurConstantsExistOnChainOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScalarHypothesesOfTopRows
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaLiftOntoOfInjectiveEigenspaces
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.WeilSiegelFormulaUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.EisRegularAtOfEisPoleLE
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SchurOrthogonalitySquareIntegrable
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.RealLowestKTypeCoeffSquareIntegrable
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.IndefiniteReal.NormalDecomposition.LiftHeckeOperators
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinRepApply
import Formalism.SharpRestriction.ElevenLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LiftIntegOfCuspRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalFixed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TransferEigensystemPartsThreeLevelsOfMultEq
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlacesOfCondition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GoodCharactersDualStableOfThetaLiftScalars
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.HeckeOperatorsRowsLiftsRationalAdjointClosed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GUnitOfModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PGEquivOfBaseW
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointLiftRangeLeGoodBlockEigenspaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftTheoremAPublishedHypothesesStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaLiftSecondHypotheses
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftTestsModularLatticeOfCoreCompatibility
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicFormNormEqAtConjugateEmbedding

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.L2.Pj Formalism.IndefR.FWT
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.PrimIn GlobalTheory.LiftRows
open GlobalTheory.Hk3 (Core Good IsSF SchurAll TwoSided FixAll EEc Wcc eH IsLab HoweUnram)

namespace GlobalTheory.LiftsOnly

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m}

section Real

variable {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL]

set_option maxHeartbeats 800000 in

theorem carries_of_upInj (hCusp : GlobalTheory.Published.CuspRapidDecay) (hHowe : HoweUnram) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hCW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hJ : GlobalTheory.Hk3.InertJunk A3) (hPG : R.PGEquiv F)
    (hUp : UpInj R.toRealDat) : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c := by
  intro c hc
  have hLI := GlobalTheory.Chain.LiftConv.liftInteg_of_cuspRapidDecay hCusp D
  have hSch : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hTw := GlobalTheory.VmTwo.twoSided_goodInert hHowe R F hLI hCW hEx hSch
  have hHk := (GlobalTheory.Hk3.inertJunk_iff A3).1 hJ
  obtain ⟨Tc, hTc, hx⟩ := _root_.GlobalTheory.UpSystem.up_sys R F hLI hOk hCW hEx hSch hTw hHk
  obtain ⟨x, hxc⟩ := hx c
  obtain ⟨w, hw, hw0⟩ := (Submodule.ne_bot_iff _).1 hc
  have hne : LinearMap.adjoint (R.Th A3.A.μ0) w ≠ 0 := fun h => hw0 (hUp A3.A.μ0 (h.trans (map_zero _).symm))
  let b := (A3.A.fam.R A3.A.μ0).S.basis
  let j := R.jX A3.A.μ0
  let op := (A3.rowI A3.A.μ0).opAll
  have hmodels := hCW.base.models
  have hjX := GlobalTheory.OneFormTest.model_jX R.toRealDat hmodels.HX hmodels.jX A3.A.μ0
  have hExt := (GlobalTheory.classPres_extMem_extBij_isom _ _ _ _ _ _ _ _ _ _ (R.B.R A3.A.μ0).pres).2.1
  have h2 : ∀ f, (R.HX A3.A.μ0).e (R.jX A3.A.μ0 f) = (R.B.R A3.A.μ0).pres.extL f := hmodels.jX A3.A.μ0
  have hli0 : LinearIndependent ℂ (fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k)) := hExt.1
  have hli : LinearIndependent ℂ (fun k => j (b k)) := by
    refine LinearIndependent.of_comp (R.HX A3.A.μ0).e ?_
    have h3 : ((R.HX A3.A.μ0).e ∘ fun k => j (b k)) =
        fun k => (R.B.R A3.A.μ0).pres.extL ((A3.A.MtildeCSD A3.A.μ0).basis k) := funext fun k => h2 _
    rewrite [h3]
    exact hli0
  have hcomm : ∀ i f, j (op i f) = Tc i (j f) := hTc
  have hpc : Formalism.L2.Col.PairComm op := (hOk.what₂ A3.A.μ0).comm
  have hso : Formalism.L2.Col.SplitOver op := by
    rintro (i | k)
    · exact (hOk.ok2.what₂ A3.A.μ0).split i
    · exact (hOk.what₂ A3.A.μ0).split k
  have hZ := (_root_.GlobalTheory.AdjBlockSpan.range_adjoint_le_span_good_block R F hLI hOk hCW hEx hSch hPG).1 A3.A.μ0
  obtain ⟨s', hxs, heig, f, hf0, hfZ, hfE⟩ := GlobalTheory.Div.exists_sys_of_mem_span D.what₂.embLL j b op Tc
    ((A3.A.fam.R A3.A.μ0).ZHg A3.A.X) hli hjX.2.2 hcomm hpc hso x (LinearMap.adjoint (R.Th A3.A.μ0) w) (hxc w hw) hne
    (hZ ⟨w, rfl⟩)
  obtain ⟨p, hp⟩ := GlobalTheory.Div.exists_ix_of_mem_eigAt A3 hOk s' f hf0 hfZ hfE
  exact ⟨p, hc, GlobalTheory.Div.map_le_span_image j (LinearMap.adjoint (R.Th A3.A.μ0)) (R.EEc c) (Formalism.L2.Col.eigAt op s')
    ((A3.rowI A3.A.μ0).inertTypeEigenspaceSum p.1)
    (fun v hv => heig.le (Formalism.L2.Col.mem_eigAt_of_forall_apply (hxc v hv))) (Formalism.L2.Col.eigAt_le_eigSum hp)⟩

theorem exists_rowPart_ne_bot_positiveDimension (hCusp : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3)
    (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hcar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) (hN : RowsNe R.toRealDat F.lv2) :
    ∃ p, R.EEp3 p ≠ ⊥ := by
  by_contra hne
  push_neg at hne
  have hc0 : ∀ c, R.EEc c = ⊥ := by
    intro c
    by_contra h
    obtain ⟨p, hp⟩ := hcar c h
    have hle : R.EEc c ≤ R.EEp3 p := by
      unfold RealDat3.EEp3
      exact le_iSup₂_of_le (f := fun c (_ : R.Carries p c) => R.EEc c) c hp le_rfl
    rw [hne p, le_bot_iff] at hle
    exact h hle
  obtain ⟨hCore, hSF, hEq, -⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hC hEx
  obtain ⟨h, -, -, htop, -⟩ := GlobalTheory.Hk3.OpsRows.exists_opsE R.toRealDat F.lv2 hCore
    (GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat) R.SF hSF
  have hbot : (⊤ : Submodule ℂ R.HE.H) = ⊥ := by
    rw [← htop]
    simp only [← hEq, hc0, iSup_bot]
  have hzero : ∀ x : R.HE.H, x = 0 := fun x => by
    have hx : x ∈ (⊤ : Submodule ℂ R.HE.H) := Submodule.mem_top
    rw [hbot] at hx
    exact (Submodule.mem_bot ℂ).1 hx
  obtain ⟨u, hu0, -⟩ := GlobalTheory.RowsPosRed.exists_row R F hC.base.models hN false
  exact hu0 (hzero (Tw.out (s := twAt D.what₂.embLL A3.A.v0) (E := R.HE.H) u))

theorem levW_of_span (hCusp : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hC : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hGS : GoodStable A3.A.X) (hCD : GlobalTheory.CuspMult.CuspDecomp D)
    (hME : GlobalTheory.CuspMult.MultEq R.toRealDat) (hBlock : (R.toCx3 F).zs.InBlock) (hCar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c)
    (hScal : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) (hA : R.PThmA) (hLT : Formalism.IndefR.Rat.LiftTest (R.toCx3 F))
    (hU : R.toRealDat.LUnif) : R.PLevW F := by
  have hSchur := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCusp R.toRealDat
  have hSpan := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hC hEx hSchur hGS hCD hME hCar
  have hW := GlobalTheory.T.principalFormsSubspace_eq_good_forms R F hOk hC hEx hSpan hScal hA hLT hBlock
  intro j
  exact (_root_.GlobalTheory.WType.range_w0C_type R F hOk hC hEx hU j).trans (congrArg (· ⊓ _) (hW j).symm)

theorem partsW_of_carried (hCRD : GlobalTheory.Published.CuspRapidDecay) (R : RealDat3 D A3 Ks) (F : Face3 D A3) {s : ℕ}
    (hOk : A3.fam3.Ok3 s) (hW : R.WeakCharacterisation F) (hEx : R.toRealDat.ExAt) (hGS : GoodStable A3.A.X) (hCD : GlobalTheory.CuspMult.CuspDecomp D)
    (hME : GlobalTheory.CuspMult.MultEq R.toRealDat) (hOkH : ∀ t, (A3.A.fam.R t).OkH ∧ (A3.rowI t).InertRationalAdjoint)
    (hcar : ∀ c, R.EEc c ≠ ⊥ → ∃ p, R.Carries p c) (hkap : 0 < R.kap ∧ ∀ i t p, 0 < R.lam3 i t p A3.A.v0) (hB : R.PThmB)
    (hU : R.toRealDat.LUnif) : (R.toCx3 F).PartsW false := by
  have hS : SchurAll R.toRealDat := GlobalTheory.Hk3.schurAll_of_cuspRapidDecay hCRD R.toRealDat
  obtain ⟨hCore, hSF, -, hWc⟩ := GlobalTheory.CoreOfWeak.core_of_weak R F hW hEx
  have hirr : ∀ χ ∈ A3.A.X, IsAbsIrrChar χ := hOk.ok2.irr
  have hspan := _root_.GlobalTheory.SpanW.iSup_wp3_eq_range_eH R F hOk hW hEx hS hGS hCD hME hcar
  have horth := _root_.GlobalTheory.OrthW.inner_wp3_eq_zero_of_ne R F hOk hW hEx hS hOkH hkap hB
  intro j
  have htype := _root_.GlobalTheory.WType.range_w0C_type R F hOk hW hEx hU j
  refine ⟨fun p q hpq w hw w' hw' => ?_, ?_⟩
  · exact GlobalTheory.SumW.inner_tw_eq_zero (E := (R.HW j (sg0 D A3.A)).H) (twAt D.what₂.embLL A3.A.v0) w w'
      (horth j p q hpq _ hw.1 _ hw'.1)
  · obtain ⟨-, -, -, -, -, hst, -⟩ := GlobalTheory.T.sphericalOperators_forms_on_rank_space_normal R.toRealDat F.lv2 hCore hS hirr R.SF hSF j
    have hstab : ∀ p g, (R.Wp3 j p).map (R.gW j (sg0 D A3.A) g) ≤ R.Wp3 j p := by
      intro p g
      unfold RealDat3.Wp3
      simp only [Submodule.map_iSup]
      exact iSup₂_mono fun c _ => by rw [hWc]; exact hst c g
    have hstabX : ∀ p g, ((R.toCx3 F).Wp j p).map (R.gWx F j g) ≤ (R.toCx3 F).Wp j p := by
      rintro p g _ ⟨y, hy, rfl⟩
      exact hstab p g (Submodule.mem_map_of_mem hy)
    have hsumX : (⨆ p, (R.toCx3 F).Wp j p) =
        Tw.sub (twAt D.what₂.embLL A3.A.v0) (LinearMap.range (eH R.toRealDat j)) :=
      (GlobalTheory.SumW.tw_sub_iSup (twAt D.what₂.embLL A3.A.v0) (R.Wp3 j)).symm.trans
        (congrArg (Tw.sub (twAt D.what₂.embLL A3.A.v0)) (hspan j))
    rw [htype]
    unfold typeSubspace
    exact GlobalTheory.SumW.iSup_inf_inf_typeSp _ (R.gWx F j) F.P0 F.ψ0⁻¹ ((R.toCx3 F).Wp j) _ hstabX hsumX

end Real

end GlobalTheory.LiftsOnly

end
