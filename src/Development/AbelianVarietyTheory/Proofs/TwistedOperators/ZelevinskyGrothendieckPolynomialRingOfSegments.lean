import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.SegmentRepresentation
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GrothendieckRingPolynomial
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ZelevinskySegmentClassExistsForEveryPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductHasFiniteLengthGL

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.JHMult

namespace GlobalTheory

theorem zelevinskyPolynomialRing_of_parts :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.SegmentRepresentation →
      GlobalTheory.Published.GrothendieckRingPolynomial → GlobalTheory.Published.ZelevinskyPolynomialRing := by
  intro hBZ hSeg hRing k _ _ _ _
  obtain ⟨Z, hZ⟩ := _root_.GlobalTheory.segmentClass_exists hSeg k
  obtain ⟨Ψ, h1, hmul, hX⟩ := hRing k Z hZ
  refine ⟨Z, Ψ, hZ, ⟨h1, fun r t V W _ _ _ _ π₁ π₂ h₁ h₂ s₁ s₂ => ?_⟩, hX⟩
  have h := _root_.GlobalTheory.ProdLength.prod₂_hasFiniteLength hBZ k r t V W π₁ π₂ h₁ h₂ s₁ s₂
  exact ⟨h, hmul r t V W π₁ π₂ h₁ h₂ s₁ s₂ h⟩

end GlobalTheory
