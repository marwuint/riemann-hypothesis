import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CurvatureFormMatrixBoundedDomainModelMetricAtZer
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.InterPolyProdSum
import Formalism.DegreeFormula.Statement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MeasurePreservingCompEquiv
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlockSymApply

set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.curvatureFormMatrix_boundedDomainModelMetric_at_zero : ∀ (ι : Type) [Fintype ι] (p q n : ℕ) (h : Fintype.card (ι × Fin p × Fin q) = n) (τ : ι), GlobalTheory.GoodMetric.curvPoly (fun u => Matrix.transpose (Formalism.DegreeFormula.hP (Formalism.DegreeFormula.unflat (GlobalTheory.UnifDens.flatL h u) τ))⁻¹) 0 = -GlobalTheory.DomainDens.blockSym h τ := by
  exact @GlobalTheory.DomainDens.curvPoly_model_zero
