import Mathlib
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Osgood
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StatementsCurrent
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.EqZeroOfMemZeroLocusLineOriginIdeal

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets

open MvPolynomial MeasureTheory Filter Topology Matrix

noncomputable section

variable {n d : ℕ}

theorem linVal_eq (u x : Fin n → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.linVal u x = GroundTheory.Heights₂.Heights.linEval u x := rfl

theorem fibre_eq (J : Ideal (MvPolynomial (Fin n) ℂ)) (A : Matrix (Fin d) (Fin n) ℂ)
    (w : Fin d → ℂ) :
    GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets.fibre J A w =
      GroundTheory.Heights₂.Heights.ComplexSets.fibre J A w := rfl

theorem analyticOnNhd_of_differentiableOn {U : Set (Fin d → ℂ)} {s : (Fin d → ℂ) → Fin n → ℂ}
    (hU : IsOpen U) (hs : DifferentiableOn ℂ s U) : AnalyticOnNhd ℂ s U := by
  have h : ∀ j, AnalyticOnNhd ℂ (fun y => s y j) U := fun j =>
    ReciprocityTheory.AnForm.Osgood.osgood d U _ hU (differentiableOn_pi.mp hs j)
  exact AnalyticOnNhd.pi h

variable {J : Ideal (MvPolynomial (Fin n) ℂ)} {A : Matrix (Fin d) (Fin n) ℂ} {x : Fin n → ℂ}

theorem maDens_congr_of_eventuallyEq {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {z : Fin D → ℂ}
    (h : ∀ k, φ k =ᶠ[𝓝 z] ψ k) :
    ReciprocityTheory.AnForm.maDens φ z = ReciprocityTheory.AnForm.maDens ψ z := by
  have hH : ∀ k, ReciprocityTheory.AnForm.hessC (φ k) z = ReciprocityTheory.AnForm.hessC (ψ k) z := by
    intro k
    have h2 : fderiv ℝ (fderiv ℝ (φ k)) z = fderiv ℝ (fderiv ℝ (ψ k)) z :=
      ((h k).fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)
    unfold ReciprocityTheory.AnForm.hessC
    rw [h2]
  unfold ReciprocityTheory.AnForm.maDens
  simp only [hH]

end

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.ComplexSets
