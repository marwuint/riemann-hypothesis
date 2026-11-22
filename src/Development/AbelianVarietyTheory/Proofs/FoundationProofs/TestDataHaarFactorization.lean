import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IntegralIndicatorProjFinSmul
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqZeroOfMemClosureSpan
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeOperatorConvolutionAndLeftTranslate
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsLocallyConstantCosetInd
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdmissibleIrreducibleTorusCharacters
open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.AutMult

section Helpers

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G] [MeasurableSpace G] [BorelSpace G]

theorem conv_cosetInd_eq_smul (μ : Measure G) [μ.IsMulLeftInvariant] (K : Subgroup G) (ho : IsOpen (K : Set G))
    (hK : IsCompact (K : Set G)) (f : G → ℂ) (hf : ∀ k ∈ K, ∀ g, f (g * k) = f g) :
    conv μ f (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 = fun y => (μ.real K : ℂ) * f y := by
  classical
  funext y
  have hs : MeasurableSet ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)) :=
    (ho.preimage (continuous_const.mul continuous_id)).measurableSet
  have e : (fun x => f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y)) =
      ((fun x => y⁻¹ * x) ⁻¹' (K : Set G)).indicator (fun _ => f y) := by
    funext x
    rw [GlobalTheory.InvBilinTest.cosetInd_apply]
    by_cases hx : y⁻¹ * x ∈ K
    · have h1 : x⁻¹ * y * 1⁻¹ ∈ K := by simpa using K.inv_mem hx
      rw [if_pos h1, Set.indicator_of_mem (show x ∈ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_one]
      have := hf _ hx y
      rwa [mul_inv_cancel_left] at this
    · have h1 : ¬ x⁻¹ * y * 1⁻¹ ∈ K := fun h => hx (by simpa using K.inv_mem h)
      rw [if_neg h1, Set.indicator_of_notMem (show x ∉ (fun x => y⁻¹ * x) ⁻¹' (K : Set G) from hx), mul_zero]
  show ∫ x, f x * (GlobalTheory.InvBilinTest.cosetInd K ho hK 1).1 (x⁻¹ * y) ∂μ = _
  rw [e, integral_indicator_const _ hs]
  simp only [Measure.real, measure_preimage_mul, Complex.real_smul]

theorem isIntegralOp_const_mul {W : Type} [AddCommGroup W] [Module ℂ W] {μ : Measure G}
    {σ : Representation ℂ G W} {f : G → ℂ} {A : W →ₗ[ℂ] W} (hA : GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ f A) (c : ℂ) :
    GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets.IsIntegralOp μ σ (fun g => c * f g) (c • A) := by
  intro v l
  refine ⟨?_, ?_⟩
  · simpa only [mul_assoc] using (hA v l).1.const_mul c
  · rw [LinearMap.smul_apply, map_smul, smul_eq_mul, (hA v l).2, ← integral_const_mul]
    simp only [mul_assoc]

end Helpers

end GlobalTheory.AutMult
