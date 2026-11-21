import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecMapApply
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.AdelicAdmissibleSmul
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.KudlaSplittingSplitUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SumSquaresNeThreeThreeAdic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilObjectsInhabited

noncomputable section

open GlobalTheory.WeilM
open scoped Matrix

namespace GlobalTheory.LinPair.Model

section General

variable {k : Type} [Field k] [Invertible (2 : k)] {E : Type} [Field E] [Algebra k E] {c : E →ₐ[k] E}
  {α β ν κ : Type} [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype ν] [DecidableEq ν] [Fintype κ]
  [TopologicalSpace k] [IsTopologicalRing k] [LocallyCompactSpace k] [TopologicalSpace E] [IsModuleTopology k E]
  {ψ : AddChar k ℂ} {ξ : E} {JA : Matrix α α E} {JB : Matrix β β E} {d : Darboux (symp c ξ JA JB) κ} {χ : Eˣ →* Circle}
  {Cy : Matrix β ν E} {om : UG c JA × UG c JB →* Module.End ℂ ((κ → k) → ℂ)} {l : ((κ → k) → ℂ) →ₗ[ℂ] ℂ}

theorem comm {G H Y : Type} [Group G] [Group H] (om : G × H →* Module.End ℂ (Y → ℂ)) (g : G) (h : H) (φ : Y → ℂ) :
    om (1, h) (om (g, 1) φ) = om (g, 1) (om (1, h) φ) := by
  rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul]; simp

end General

end GlobalTheory.LinPair.Model

end
