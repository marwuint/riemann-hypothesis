import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilConvergenceOfKernel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchroedingerOperatorHeisenbergPreservesSchwartzB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitPlaceAdelicMatrixGivenComponents
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicTraceSupportedAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianSelfDualLatticeSpaceFormHermitianNondeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianSplitSymplecticPair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchrodingerInvariantFunctionalsLagrangian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerTransitive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscriminantMulTraceDualIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticChangeOfGoodModelsIntertwines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BlockScaledIntegralOfLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSiegelDomainReduction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnramifiedCharacterAtUniformizer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterOfIdeleClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeValueNotFiniteOrder
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SplitPrimeDegreeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SubMemTwistSpan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankSB
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LeviRep
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegrableZetaIntegrand
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactCoveredByOpenCosets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StoneVonNeumannSchwartzBruhatTransverseLagrangia
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalUnipotentAdditive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitCompletelyAuxiliaryPlaceOutsideFinset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ComplementaryAdelicSchwartzOfNonzeroLocal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceSymplecticSelfZeroSplitSupported
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHomSuppSplit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftVOneMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensFormBox
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsSchwartzBruhatConvolutionLocalFieldPower
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsTranslationInvariantFunctional
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterNormOneUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DistribHaarCharSupportedIdeleEqLocalAbsValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLocalGLEmbeddingUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearWeilFunctionalTranslationEquivariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IndicatorIntMMemSB
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLocalUnitaryActionPreserves
import GroundTheory.LocalFields.LocalFourierHaar
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HaarMapLinearScalingByDeterminant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryElementActsLocalOperatorAtPlace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SwapNegApply
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocIsoRefl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GoodSplitPlaceTranslationActsThroughWeil
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearFormEqZeroOfKillsProductSchwartzBruhat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalIdempotentCharacterValue
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelLocalTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdmittedDiagonalIntegralLinearForm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ContinuousCharactersLocallyConstantNonarchLocalF
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LastColsVal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InducedFullRankIrreducible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicPlaceDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMomentMatrixTransform
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SymplecticFormUnitaryInvariant
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalMatrixMomentSurjectiveConj
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanThetaLocalAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleLatticeInvariantSchwartzGlobal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InertPlaceSchwartzBruhatVacuumConditionEqSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaLocalFactorFinitePlace

noncomputable section

namespace GlobalTheory.ThKConst

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

theorem isHecke_div {χ₁ χ₂ : Chr F E} (h₁ : IsHecke F E χ₁) (h₂ : IsHecke F E χ₂) : IsHecke F E (χ₁ / χ₂) := by
  obtain ⟨c₁, t₁⟩ := h₁
  obtain ⟨c₂, t₂⟩ := h₂
  have e : ⇑(χ₁ / χ₂) = fun x => χ₁ x / χ₂ x := funext fun x => MonoidHom.div_apply χ₁ χ₂ x
  exact And.intro (by rw [e]; exact c₁.div' c₂) fun x => by rw [MonoidHom.div_apply, t₁ x, t₂ x, div_one]

theorem resEtaPow_div {K : Subgroup (AF F)ˣ} {χ₁ χ₂ : Chr F E} {n₁ n₂ n : ℕ} (h₁ : ResEtaPow K χ₁ n₁)
    (h₂ : ResEtaPow K χ₂ n₂) (he : Even (n₁ + n₂)) (hn : Even n) : ResEtaPow K (χ₁ / χ₂) n := by
  intro x
  have e₁ := h₁ x
  have e₂ := h₂ x
  rw [MonoidHom.div_apply, Circle.coe_div, e₁, e₂]
  split_ifs
  · norm_num
  · rcases Nat.even_or_odd n₁ with h | h
    · rw [h.neg_one_pow, ((Nat.even_add.mp he).mp h).neg_one_pow, hn.neg_one_pow]
      norm_num
    · have h' : Odd n₂ := Nat.not_even_iff_odd.mp fun h'' => (Nat.not_even_iff_odd.mpr h) ((Nat.even_add.mp he).mpr h'')
      rw [h.neg_one_pow, h'.neg_one_pow, hn.neg_one_pow]
      norm_num

variable {a a' : ℕ}

theorem isPair_small {B : Base F E} {G : Geo σ a a'} {X : Chars F E} {om : Rep σ G.V G.W} {om' : Rep σ G.V' G.W}
    (h : IsTriple B G X om om') :
    IsPair B G.M' X.α (X.α / X.β) om' G.q (a' - G.q) (a + a' - (G.p + G.q)) (G.p + G.q) :=
  { base := h.base
    herm := h.geo.hV'
    skew := h.geo.hW
    good := h.geo.hM'
    hX := h.chars.heckeα
    hW := isHecke_div h.chars.heckeα h.chars.heckeβ
    resX := h.chars.resα
    resW := resEtaPow_div h.chars.resα h.chars.resβ (Nat.even_add.mpr (Nat.even_add.mp h.geo.even).symm) h.geo.even
    weil := h.weil' }

theorem thetaSum_sum {κ ι : Type} [Fintype κ] (s : Finset ι) (f : ι → (κ → AF F) → ℂ) (hf : ∀ k ∈ s, f k ∈ schA F κ) :
    thetaSum F (∑ k ∈ s, f k) = ∑ k ∈ s, thetaSum F (f k) := by
  classical
  revert hf
  refine Finset.induction_on s (fun _ => ?_) ?_
  · simp [thetaSum]
  · intro k s hk ih hf
    have hs : ∀ j ∈ s, f j ∈ schA F κ := fun j hj => hf j (Finset.mem_insert_of_mem hj)
    rw [Finset.sum_insert hk, Finset.sum_insert hk,
      thetaSum_add F (hf k (Finset.mem_insert_self k s)) (Submodule.sum_mem _ hs), ih hs]

end GlobalTheory.ThKConst
