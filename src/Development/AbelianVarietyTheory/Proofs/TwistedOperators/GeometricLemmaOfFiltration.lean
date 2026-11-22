import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.GeometricLemmaCellSemisimplificationGL

namespace GlobalTheory

theorem geometricLemma_of_filtration :
    GlobalTheory.Published.BernsteinZelevinskyFiniteness → GlobalTheory.Published.GeometricLemmaFiltration →
      GlobalTheory.Published.GeometricLemma := by
  intro hB hF k _ _ _ _
  exact ⟨hF k, _root_.GlobalTheory.SmGL.CellSemis.cellSemisimplification hB k⟩

end GlobalTheory
