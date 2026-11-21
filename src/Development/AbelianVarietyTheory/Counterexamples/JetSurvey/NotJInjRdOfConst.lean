import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.JInjRdOf
import Formalism.LocalToGlobal.ProjectiveLattices.ReadQuot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FramedModuliAlgebraicLawsChartWeightIntegrality
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsFramedPointBaseChangeAlgebraMap
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional

noncomputable section

namespace GlobalTheory.ReadingIndependence

open NumberField MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra
open ReciprocityTheory.ChartRestriction.G.PullbackSections Formalism.L2.Theta Formalism.BasicNotions.TH

theorem jInjRd_of_laws {D : D7} (T : Top D) (hM : LawsM T.toCore) {j : ℕ} (hj : InR D j)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) : JInjRd T j a n := by
  have hS : ReciprocityTheory.ChartRestriction.G.Out.SecBaseChangeSt := GlobalTheory.abelianSchemeLaws_all.1.secBaseChange
  refine jInjRd_of_wt T hM hj a n (fun p y ψ => ?_)
    (GlobalTheory.Frames.algebraic_laws hS _ _ _ _ (T.Q.Xo j) T.Q.c).2.2.2.1
  exact GlobalTheory.Frames.FramedBaseChange.exists_frMap hS _ _ _ _ (T.Q.Xo j) T.Q.c _ _ ψ y

end GlobalTheory.ReadingIndependence
