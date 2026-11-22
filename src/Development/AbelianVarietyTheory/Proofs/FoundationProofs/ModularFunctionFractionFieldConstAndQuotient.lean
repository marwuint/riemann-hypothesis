import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MdifferentiableOfHasSomeLevelOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemModularFunctionRingOverIffHasSomeLevelOver
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FractionFieldExtClosureInjective
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_const_and_quot : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (T : Frac Ω ε), (∀ c : Ω, T.an (algebraMap Ω T.K c) = ((fun _ => ε c : ℂ → ℂ) : Mero)) ∧ ∀ f : T.K, ∃ a b : ℂ → ℂ, DifferentiableOn ℂ a Hs ∧ DifferentiableOn ℂ b Hs ∧ (b : Mero) ≠ 0 ∧ T.an f * (b : Mero) = (a : Mero) := by
  intro Ω _ _ _ ε T
  have hmem := _root_.GlobalTheory.FN.mem_ring_iff_inR ε.range
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs := fun a =>
    ((_root_.GlobalTheory.FN.germ_ringHom_and_restrict).2.1 _).1 (_root_.GlobalTheory.FN.inR_mdifferentiable ε.range _ ((hmem.1 _).1 a.2))
  refine ⟨fun c => ?_, fun f => ?_⟩
  · have hc : (fun _ : ℍ => ε c) ∈ ring ε.range := (hmem.1 _).2 (hmem.2 _ ⟨c, rfl⟩)
    rw [← T.io_c c ⟨_, hc⟩ rfl, T.an_io]
    rfl
  · obtain ⟨a, b, hb, h⟩ := T.io_surj f
    refine ⟨up (a : ℍ → ℂ), up (b : ℍ → ℂ), hdiff a, hdiff b, ?_, ?_⟩
    · intro h0
      have h1 : T.an (T.io b) = T.an (T.io 0) := by
        rw [T.an_io, map_zero, map_zero]; exact h0
      exact hb (T.io_inj ((_root_.GlobalTheory.FN.frac_ext_clo_inj Ω ε T).2.2.2 h1))
    · have := congrArg T.an h
      rw [map_mul, T.an_io, T.an_io] at this
      exact this

end GlobalTheory.FN
