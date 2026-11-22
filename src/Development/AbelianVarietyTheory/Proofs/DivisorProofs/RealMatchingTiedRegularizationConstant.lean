import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Imports
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ExistsMatchOver
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialRouteSubmodule
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchLinear
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchOnto
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchOfPolMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqSmulOfStableGraph
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchKapX
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolMatchDer
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfThetaDistributionHeisenbergTranslates
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompactUnitaryPreservesPolynomialFock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLiftLeftInvariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HermitianSkewModelGood
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParameterSubgroupTransposeGramRealPlace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OneParamSubgroupTransposeGramUnitaryDecomposes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilCompositionLines
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingMellin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingInnerProduct
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SumPureMemAlgD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinitePlaceUnitaryPointKeepsZeroMatchedData
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AlgebraicDataUnitaryRelationsFinitePlacePolZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsKernelIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsAlgebraicDatumNotMatchedZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PolynomialMatchZeroIffPureTensorImageZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalHom
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLift
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsIntertwining
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearModelUnitaryConjugate
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatrixExtendByZeroZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicIntertwine
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharEqAddEquivAddHaarChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubleScalingIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HoweDualityRealPlacesTrivialCharFockLiftSmallPaiStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsGaussianKernel
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MatchedMapsFiniteIdentity
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemKerPD
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaCorrespondenceModuleMap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingConstant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TransposeGramUnitarySurjectiveFinitePlaceSupport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingAdelicVolume
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingLimit
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SeesawUnfoldingEvaluation
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RankSchwartzBruhatFinitePlaceCompletionLeAleph0
import Development.AbelianVarietyTheory.Definitions.Divisors.RegConst
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilConvergenceOfSiegelSet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsStableComplementOfIrreducibleSpanIntertwin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SimpleQuotientsIsoOfIntertwinedSemisimple
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.OrientedPairFockMapsLieEquivariant
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelRationalStructure
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ComplementaryAdelicSchwartzArchimedeanReplace
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelCharacterMatch
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilModelFiniteExponent
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsWeilModelOfExponents
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LsumMapDomainSome
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FinFLin
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaIntegralsOfMinguez

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx
open MeasureTheory GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.ChainFr Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GridFrameExistence

open GlobalTheory.SquareComm GlobalTheory.SquareDict GlobalTheory.SquareAgree GlobalTheory.Grid

variable {D : D7}

theorem fr_eq_of_onb {V : HSp D} {A A' : Fr V} (h : ∀ τ, A.onb τ = A'.onb τ) : A = A' := by
  have hf : A.fr = A'.fr := funext fun τ => by
    have h1 := congrArg (·⁻¹) (h τ)
    simp only [Fr.onb] at h1
    rwa [Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A.fr_unit τ)),
      Matrix.nonsing_inv_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det _).1 (A'.fr_unit τ))] at h1
  have he : A.ε = A'.ε := funext fun τ => by
    have h1 : (A.fr τ)ᴴ * Formalism.REAL.Jm (A.ε τ) * A.fr τ = (A.fr τ)ᴴ * Formalism.REAL.Jm (A'.ε τ) * A.fr τ := by
      rw [A.fr_gram, hf, A'.fr_gram]
    have u := A.fr_unit τ
    have u' : IsUnit (A.fr τ)ᴴ := (Matrix.isUnit_conjTranspose _).2 u
    have h2 := u'.mul_left_cancel (u.mul_right_cancel h1)
    funext a
    have h3 := congrFun (congrFun h2 a) a
    cases h4 : A.ε τ a <;> cases h5 : A'.ε τ a <;> simp [Formalism.REAL.Jm, h4, h5] at h3 ⊢ <;> norm_num at h3
  cases A
  cases A'
  simp only at hf he
  subst hf he
  rfl

theorem gridFr_unique {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {X : Node} {A A' : Fr (G.V X)}
    (h : IsGridFr W X A) (h' : IsGridFr W X A') : A = A' :=
  fr_eq_of_onb fun τ => (h τ).1.trans (h' τ).1.symm

open GlobalTheory.SquareConv in

theorem standing_of_size {large₂ : SizeData₂ D} (hs : GlobalTheory.IndefiniteRowSideFullHecke.LevelPlusSubgroup.SizeRows large₂) (hx : 11 ≤ D.host.splitBound) {T : Type}
    {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) {sc : Consts} (G : GridData L sc) (t : T) : SquareStanding G t := by
  classical
  have hcc : D.host.ccK = ⊤ := hs.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨⟨P, -, -⟩, -⟩ := hs
  have lev : ∀ p ∈ D.host.levelPrimes, p.Prime → Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := fun p hp hpp =>
    UpperTheory.Ram.Fun.coprime_condN_of_splitK D.host hpp (P.level_split p hp)
  refine ⟨hx, fun w hw => ?_⟩
  have e1 : ((D.host.QS * D.host.q * D.host.d * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) =
      ((D.host.QS * D.host.q * D.host.d : ℕ) : 𝓞 D.host.E) := by
    rw [hcc, Ideal.absNorm_top, mul_one]
  rw [e1]
  rcases Finset.mem_union.1 hw with hw | hw
  · obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hw
    obtain ⟨p, hpv, hcop⟩ : ∃ p : ℕ, ((p : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal ∧ Nat.Coprime p (D.host.QS * D.host.q * D.host.d) := by
      rcases G.pl.mem_S0_of_sum_eq.1 hv with rfl | hv1
      · refine ⟨q0 D, G.pl.basePlace_over_qZero, ?_⟩
        have hs := (leastSplitAuxiliaryPrimeThetaChain_spec D).2.1
        have hM : Nat.Coprime (Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D) (q0 D) := by
          rw [Nat.Coprime, Nat.gcd_rec, hs, Nat.gcd_one_left]
        have hdv : D.host.QS * D.host.q * D.host.d ∣ Formalism.MainNotions.rPrAv D * LevelStarExponents.condE D := by
          unfold LevelStarExponents.condE
          exact Dvd.dvd.mul_left dvd_rfl _
        exact (hM.coprime_dvd_left hdv).symm
      · rcases (S1_mem_OmF D).1 hv1 with h | h | h | h
        · exact ⟨_, h, lev _ (D.host.g_level 0) (D.host.g_prime 0)⟩
        · exact ⟨_, h, lev _ (D.host.g_level 1) (D.host.g_prime 1)⟩
        · exact ⟨_, h, lev _ D.host.pde_level.1 D.host.pde_prime⟩
        · exact ⟨_, h, lev _ D.host.pde_level.2 D.host.pde'_prime⟩
    have hpw : ((p : ℕ) : 𝓞 D.host.E) ∈ (G.pl.w v).asIdeal := by
      rw [← G.pl.under_w hv, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at hpv
      exact hpv
    exact natCast_not_mem (G.pl.w v).isPrime.ne_top hcop hpw
  · intro hmem
    apply (hL.Q_off t w hw).1
    rw [Nat.cast_mul]
    exact Ideal.mul_mem_right _ _ hmem

end GlobalTheory.GridFrameExistence

end
