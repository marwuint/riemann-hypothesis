import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.InducedCellSemisimplification
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.JacquetOfInducedFiltration

namespace GlobalTheory.CompanionTheory.GeoLink

theorem geometricLemma : GlobalTheory.Published.GeometricLemma := by
  intro k _ _ _ _
  have h := _root_.GlobalTheory.CompanionTheory.Glob.cellSemisimplification k
  have hloc := GlobalTheory.T.jacquetOfInducedFiltration' k
  first
    | exact h hloc
    | exact h.mpr hloc
    | exact ⟨h, hloc⟩
    | exact ⟨hloc, h⟩
    | exact hloc.mpr h
    | exact hloc h
    | exact hloc

end GlobalTheory.CompanionTheory.GeoLink
