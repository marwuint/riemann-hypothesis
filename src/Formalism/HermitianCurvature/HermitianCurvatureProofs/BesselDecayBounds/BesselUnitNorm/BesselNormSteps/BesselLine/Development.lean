import Formalism.HermitianCurvature.HermitianCurvatureProofs.BesselDecayBounds.BesselUnitNorm.BesselLine

open MeasureTheory Matrix Finset
open scoped InnerProductSpace

noncomputable section

namespace PI.WBL

open Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.ThB Formalism.BasicNotions PI.BesselLine

def Eventually (P : D7 → ℝ → ℝ → ℝ → Prop) : Prop :=
  ∀ Ch Cq : ℝ, ∃ Cg₀ : ℝ, ∀ Cg : ℝ, Cg₀ ≤ Cg → ∀ D : D7, P D Ch Cg Cq

theorem Eventually.and {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P) (hQ : Eventually Q) :
    Eventually (fun D Ch Cg Cq => P D Ch Cg Cq ∧ Q D Ch Cg Cq) := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  obtain ⟨b, hb⟩ := hQ Ch Cq
  exact ⟨max a b, fun Cg h D => ⟨ha Cg (le_trans (le_max_left _ _) h) D, hb Cg (le_trans (le_max_right _ _) h) D⟩⟩

theorem Eventually.mono {P Q : D7 → ℝ → ℝ → ℝ → Prop} (hP : Eventually P)
    (h : ∀ D Ch Cg Cq, P D Ch Cg Cq → Q D Ch Cg Cq) : Eventually Q := by
  intro Ch Cq
  obtain ⟨a, ha⟩ := hP Ch Cq
  exact ⟨a, fun Cg hc D => h _ _ _ _ (ha Cg hc D)⟩

end PI.WBL
