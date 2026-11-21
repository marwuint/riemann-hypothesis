import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsDeltaDelAtOwnAt
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsCoreJOfChiOKNoVol
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.XiValIffXiAt
import Formalism.LocalToGlobal.ProjectiveLattices.DepthTie
import Development.AbelianVarietyTheory.Definitions.Jets.EmbShortThLeThetaPlain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTwistPlacesAboveK
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LFunctionPositiveConductorFourEight
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AssembleLattice
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.JointQ
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.SetUnipotentTranslate
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeCoprimeSmallConductor
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsExplicitParameters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsLevChOfLevelPrime
import Formalism.GL3MeanSquares.PrimeCountAsymptoticInProgressions
import Development.AbelianVarietyTheory.Definitions.Foundations.RayPrimes
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplZeta
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExplChi
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LogDerOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ZeroCount
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Jutila
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.PageThm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.IsExcRat
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.QuadraticHeckeZeroEstimates
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LogCondLeThree
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.AuxiliaryPrimeMemAvoidedPrimes
import Formalism.SharpRestriction.InertJacobiLevels.HostFam
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ScalePolynomialQuantitiesComparison
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExplicitRanksBasicBoundsLargeScale
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.ThickExists
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LogAddRpowMulLogPowLeRpow
import Development.AutomorphicArithmetic.ThickFrames.ThickFrame2Large
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DivLeRpowThreeQuarters
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormOnePrimeElements
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NcardPrimesOverOfStabilizer
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.KroneckerTwoNegEqJacobiSymTwo
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRanksRankValFrame
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.NonemptyFieldAxiomsCyclicPow
import Development.AutomorphicArithmetic.CharacterBoxes.RealSplit
import Development.AutomorphicArithmetic.MeanSquareBounds.IndUnique
import Formalism.GL3MeanSquares.HookFormulaTorsion.GlobalBoundRefinements
import Formalism.CyclotomicNorms.StatementI
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImagQuadIntegers
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ClassNumberLeAbsDiscrOfFinrankEqTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RayClassNumberBounds
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimeIdealsCountingBounds
import Formalism.GL3MeanSquares.SmoothedRemainderRealIntegralFormula
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogFactorialEqSumVonMangoldtMulDiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LogDerivSeriesOfExplicit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZerosInWindowFiniteAndPosOrder
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DirichletLZeroSymmetry
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumIndicatorLeZsumR
import Formalism.GL3MeanSquares.HookFormulaTorsion.PrimesInProgressionCountLowerBound
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumVonMangoldtLeTwoMul
import Development.AutomorphicArithmetic.MeanSquareBounds.Thin
import Development.AutomorphicArithmetic.MeanSquareBounds.SmallZeros
import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Development.AutomorphicArithmetic.PrimitiveCosets.ToEBij
import Development.AutomorphicArithmetic.MeanSquareBounds.realCond
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsRefill
import Formalism.LocalRingCardinality.HostCls
import Development.AutomorphicArithmetic.ThickFrames.topsBase
import Formalism.FrobeniusOrbits.HostCorollaries
import Formalism.SharpRestriction.GlobalSchurBounds.MainIn
import Formalism.SharpRestriction.GlobalSchurBounds.ZetaZeroFreeRegion
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ChoiceOfTops
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SzRowNumAt
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsStdLarge
import Development.AbelianVarietyTheory.Proofs.HeightProofs.XLeZBaseOfPowLeN
import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ConjugateEmbApply
import Development.AbelianVarietyTheory.Proofs.HeightProofs.JointQOfSmallField
import Development.AbelianVarietyTheory.Proofs.HeightProofs.HostSzOfSizes
import Development.AbelianVarietyTheory.Proofs.HeightProofs.ExistsIsRayIntermediateField
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevGapSplit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsPreHasLetters
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.StandardFrameOfDiagonalStages
import Development.AbelianVarietyTheory.Definitions.HeightFunctions.IntUnit
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CompletelySplitPrimeHostPlaceProperties
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow

set_option autoImplicit false

noncomputable section

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.FWT
open GlobalTheory.FinalJoin GlobalTheory.FinalJoin2 GlobalTheory.RealIndexBound GlobalTheory.BigOn.Inhab

namespace GlobalTheory.BigOn

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem level_of_is {T : Core D} (hT : LawsM T) {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) (hO : T.pb = Lc.C.P.pb) :
    T.Q.l.Mb = ∏ PP ∈ Lc.Pg, PP.asIdeal := by
  have hprod := T.Q.l.prod
  refine GlobalTheory.CoverHalf.eq_prod_of_squarefree ?_ _ fun PP => ?_
  · rw [hT.pins.2.1.1] at hprod
    exact (hprod ▸ GlobalTheory.CoverHalf.squarefree_span_g D : Squarefree (T.Q.l.Mb * _)).of_mul_left
  · rw [hL.Pg, hT.half.2, GlobalTheory.CoverHalf.prod_map_le_iff, hO]
    rfl

theorem exists_half_of_is {Lc : LevCh D T0} {μ0 : T0} (hL : Lc.Is μ0) {p : ℕ} (hp : p = D.host.pde ∨ p = D.host.pde') :
    ∃ P : HeightOneSpectrum (𝓞 D.host.K), (p : 𝓞 D.host.K) ∈ P.asIdeal ∧ ∀ t, ∀ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal →
      P.asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  obtain ⟨P, hP⟩ := hL.Q_de p hp
  by_cases h : ∃ t, ∃ PP ∈ Lc.Q t, (p : 𝓞 D.host.E) ∈ PP.asIdeal
  · obtain ⟨t, PP, h1, h2⟩ := h
    refine ⟨P, ?_, fun t PP h1 h2 => ?_⟩
    · rw [← hP t PP h1 h2]
      change algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (p : 𝓞 D.host.K) ∈ PP.asIdeal
      rwa [map_natCast]
    · rw [← hP t PP h1 h2]
      exact Ideal.map_comap_le
  · have hpp : p.Prime := by
      rcases hp with rfl | rfl
      exacts [D.host.pde_prime, D.host.pde'_prime]
    obtain ⟨P', hP'⟩ := GlobalTheory.exists_heightOneSpectrum_natCast_mem D.host.K hpp
    exact ⟨P', hP', fun t PP h1 h2 => absurd ⟨t, PP, h1, h2⟩ h⟩

theorem ownAt_special (v : HeightOneSpectrum (𝓞 D.what₂.LL)) : ownAt D v = D.host.pde ∨ ownAt D v = D.host.pde' := by
  unfold ownAt
  split_ifs
  exacts [Or.inr rfl, Or.inl rfl]

theorem oneHalf_of_is {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) {μ0 : T0}
    (hL : R.toLevCh.Is μ0) : ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v,
      ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧ ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
        (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal := by
  classical
  choose P h1 h2 using fun (p : ℕ) (hp : p = D.host.pde ∨ p = D.host.pde') => exists_half_of_is hL hp
  refine ⟨fun p => if hp : p = D.host.pde ∨ p = D.host.pde' then P p hp else R.C.P.pb 0, fun v => ?_⟩
  simp only [dif_pos (ownAt_special v)]
  refine ⟨h1 _ _, fun PP hPP => ?_⟩
  have h3 := Finset.mem_filter.1 hPP
  exact h2 _ _ _ PP h3.1 h3.2

theorem level_and_oneHalf (J : CoreJ D) [Algebra J.Q.c.F D.what₂.LL] (R : RealDat D A J.Q.c.F) (μ0 : T0) (hL : R.toLevCh.Is μ0)
    (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) :
    J.Q.l.Mb = ∏ PP ∈ R.Pg, PP.asIdeal ∧
      ∃ Pk : ℕ → HeightOneSpectrum (𝓞 D.host.K), ∀ v ∈ R.twPl, ((ownAt D v : ℕ) : 𝓞 D.host.K) ∈ (Pk (ownAt D v)).asIdeal ∧
        ∀ PP ∈ GlobalTheory.OnTies.placesOver R (R.mu v) (ownAt D v),
          (Pk (ownAt D v)).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) ≤ PP.asIdeal :=
  ⟨level_of_is hc.toLawsM hL hO, (oneHalf_of_is R hL).imp fun _ h v _ => h v⟩

theorem coreTies_of_is {L : SizeData₂ D} {EX : ErrX D} {J : CoreJ D} [Algebra J.Q.c.F D.what₂.LL] {R : RealDat D A J.Q.c.F} {μ0 : T0}
    (hL : R.toLevCh.Is μ0) (hO : J.pb = R.C.P.pb) (hc : LawsCore J.toCore) (hcan : J.Q.Canon)
    (hr : ∀ j, 1 ≤ (J.Q.Dw j).p + (J.Q.Dw j).q) (hE : HalfEX J.toCore EX) (h₁ : FieldOK0 D D.host.pde)
    (h₂ : FieldOK0 D D.host.pde') (hs : FieldSmall D L) (hd : ∀ x, ((R.C.del.1 x : ℂˣ) : ℂ) ∈ FO D)
    (hd' : ∀ x, ((R.C.del'.1 x : ℂˣ) : ℂ) ∈ FO D) : CoreTies L EX J R :=
  ⟨hc, hcan, hr, hE, h₁, h₂, hs, (level_and_oneHalf J R μ0 hL hO hc).1, (level_and_oneHalf J R μ0 hL hO hc).2, hd, hd'⟩

end GlobalTheory.BigOn

end
