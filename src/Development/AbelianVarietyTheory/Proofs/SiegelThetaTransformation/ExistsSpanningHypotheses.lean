import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsBaseClassLevelAdapted
import Formalism.LocalToGlobal.ProjectiveLattices.CuspFree
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.AnChartAsm
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedPointReducedFromTestRing
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ShortValTotOfPinned
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.ExistsIsNab
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelMulSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDeltaDatumHigherLevel
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsEquivariantFunOnSpanningFamilies
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsDatumSumAndAllSignatures
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLevelGoodAtAllPrimesAndIdx
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CongrOfDvdModulus

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level
open GlobalTheory.SW hiding Level
open Formalism.L2.Pj Formalism.L2.PjFree
open scoped ComplexConjugate Classical
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Dict

namespace GlobalTheory.SpanInhab

theorem exists_imag_neg {E : Type} [Field E] [NumberField E] [IsCMField E] (H : Host E) :
    ∃ ξ : E, cc ξ = -ξ ∧ ξ ≠ 0 ∧ ∀ τ : E →+* ℂ, τ (H.rt : E) = H.rt0 → (τ ξ).im < 0 := by
  have hd : (0 : ℝ) < H.d := by exact_mod_cast H.d_prime.pos
  have key : ∀ z : ℂ, z ^ 2 = -(H.d : ℂ) → z.re = 0 ∧ z.im ≠ 0 := by
    intro z hz
    have h1 := congrArg Complex.re hz
    have h2 := congrArg Complex.im hz
    simp [sq] at h1 h2
    have him : z.im ≠ 0 := by
      intro h; rw [h] at h1; nlinarith [mul_self_nonneg z.re]
    refine ⟨?_, him⟩
    have : z.re * z.im = 0 := by linarith
    exact (mul_eq_zero.1 this).resolve_right him
  have hE : ((H.rt : E)) ^ 2 = -(H.d : E) := by
    have := congrArg (fun z : 𝓞 E => (z : E)) H.rt_sq
    simpa using this
  have hcc : cc (H.rt : E) = -(H.rt : E) := by
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    apply τ.injective
    have hk := key (τ (H.rt : E)) (by rw [← map_pow, hE, map_neg, map_natCast])
    have : τ (cc (H.rt : E)) = starRingEnd ℂ (τ (H.rt : E)) := IsCMField.complexEmbedding_complexConj E τ _
    rw [this, map_neg]
    apply Complex.ext <;> simp [hk.1]
  have h0 : (H.rt : E) ≠ 0 := by
    intro h
    rw [h] at hE
    have : (H.d : E) = 0 := by linear_combination hE
    exact H.d_prime.ne_zero (by exact_mod_cast this)
  rcases lt_or_gt_of_ne (key _ H.sqrt_neg_disc_sq).2 with h | h
  · exact ⟨H.rt, hcc, h0, fun τ hτ => hτ ▸ h⟩
  · refine ⟨-(H.rt : E), ?_, neg_ne_zero.2 h0, fun τ hτ => by rw [map_neg, hτ]; simpa using h⟩
    have : cc (-(H.rt : E)) = -cc (H.rt : E) := by simp [cc]
    rw [this, hcc]

end GlobalTheory.SpanInhab
