import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ParabolicLeviDecomposition
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralizerRegularLeviCommutativeNoncompactStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TypeHypothesisFormsAgreeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LeviMonotoneInParabolic
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ArchimedeanIwasawaDecomposition
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularCentralizerNoncompact
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RegularSemisimpleTestVanishing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConjMemStandardLeviOfReducibleCharpoly
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NilpotentEqZeroOfCommuteSepAlg

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.SplitTorusZero

open GlobalTheory.TruncKer GlobalTheory.IndefiniteRowSideFullHecke.NonFieldTypeVanishingAlt GlobalTheory.Chamber GlobalTheory.Cusp

variable {D : D7} {V : HSp D}

theorem rat_mem_GQ (g : GF V) : rat V g ∈ GQ V := by
  rw [GlobalTheory.AdelicU.GQ_eq, ← GlobalTheory.AdelicU.range_ratEmb]; exact ⟨g, rfl⟩

theorem zeroClause_of_conj (μ : Measure (GA D V)) (f : GA D V → ℂ) (γ g : GF V)
    (h : ZeroClause μ f (rat V (g * γ * g⁻¹))) : ZeroClause μ f (rat V γ) := by
  have hg := rat_mem_GQ g
  have e : ratClass (GQ V) (rat V (g * γ * g⁻¹)) = ratClass (GQ V) (rat V γ) := by
    ext δ
    simp only [ratClass, Set.mem_ofPred_eq, map_mul, map_inv]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨(rat V g)⁻¹ * k, mul_mem (inv_mem hg) hk, by group⟩
    · rintro ⟨k, hk, rfl⟩
      exact ⟨rat V g * k, mul_mem hg hk, by group⟩
  intro 𝓕 h𝓕
  have := h 𝓕 h𝓕
  unfold HasClassInt classKernel at *
  rw [e] at this
  exact this

theorem summable_class {f : GA D V → ℂ} (hf : HasCompactSupport f) {γ : GA D V} (hγ : γ ∈ GQ V) (x : GA D V) :
    Summable fun δ : ratClass (GQ V) γ => f (x⁻¹ * δ * x) := by
  have hmem : ∀ δ : ratClass (GQ V) γ, (δ : GA D V) ∈ GQ V := fun ⟨δ, k, hk, e⟩ => e ▸ mul_mem (mul_mem (inv_mem hk) hγ) hk
  let ι : ratClass (GQ V) γ → GQ V := fun δ => ⟨δ, hmem δ⟩
  have hι : Function.Injective ι := fun a b e => Subtype.ext (congrArg (fun z : GQ V => (z : GA D V)) e)
  apply summable_of_hasFiniteSupport
  refine ((GlobalTheory.AutomorphicL2Unitary.finite_support_kernel (Γ := GQ V) hf x x).preimage hι.injOn).subset ?_
  intro δ hδ
  exact hδ

theorem fd_of_quot {μ : Measure (GA D V)} [μ.IsHaarMeasure] {𝓕 : Set (GA D V)} (h𝓕 : IsFundamentalDomain (GQ V) 𝓕 μ)
    {φ : GA D V → ℂ} (hφ : GlobalTheory.AutomorphicL2Unitary.LeftInv (GQ V) φ) (hi : Integrable (descend (GQ V) φ) (autMeasure V μ)) :
    IntegrableOn φ 𝓕 μ ∧ ∫ x in 𝓕, φ x ∂μ = ∫ q, descend (GQ V) φ q ∂autMeasure V μ := by
  refine ⟨?_, ?_⟩
  · have := (GlobalTheory.AutomorphicL2Unitary.memLp_quotMeasure_iff h𝓕 (p := 1)).1 (memLp_one_iff_integrable.2 hi)
    rw [hφ.lift_descend] at this
    exact memLp_one_iff_integrable.1 this
  · rw [GlobalTheory.AutomorphicL2Unitary.integral_quotMeasure h𝓕]
    exact congrArg (fun F => ∫ x in 𝓕, F x ∂μ) hφ.lift_descend.symm

end GlobalTheory.SplitTorusZero
