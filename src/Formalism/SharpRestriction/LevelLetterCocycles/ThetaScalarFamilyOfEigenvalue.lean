import Formalism.SharpRestriction.GlobalTheoremInputs
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
import Formalism.SharpRestriction.LevelLetterCocycles.StatementFamilies.ExportFamilies
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.CuspSpanNormBounds.PlaceDegreeData
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets

noncomputable section

namespace Formalism.MainNotions.N

open Formalism.BasicNotions Formalism.MainNotions Filter Topology

theorem export_link_of_family {eps : ℝ} (Fm : FamP eps) (h : Formalism.MainNotions.TwistedPlaces.OrbitValuationBound Fm) : LinkN Fm := by
  obtain ⟨C, x0, hx⟩ := h
  refine ⟨C, x0, fun x hx0 i hsha j hj hS => ?_⟩
  have hp := hx x hx0 i
  unfold TwistedPlaces.aux₃ at hp
  exact hp hsha hS j hj

theorem linkN_of {eps : ℝ} (Fm : FamP eps) (hA : Formalism.MainNotions.TwistedPlaces.AdmF Fm) (hS : Formalism.MainNotions.TwistedPlaces.KudlaFamilyStatement Fm) :
    LinkN Fm := export_link_of_family Fm (hS hA)

theorem eps_pos {eps : ℝ} (Fm : FamP eps) : 0 < eps := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i).sc.eps_pos
  rwa [Fm.L_eps] at h

theorem eps_lt {eps : ℝ} (Fm : FamP eps) : eps < 1 / 52 := by
  obtain ⟨i⟩ := Fm.Ix_zero
  have h := (Fm.L 0 i).sc.eps_lt
  rwa [Fm.L_eps] at h

def LamPos (D : D7) (μ : D.what₂.Tup) (j : ℕ) : Prop :=
  ∀ σ : D.what₂.FT,
    (∀ f ∈ D.what₂.isot j σ, D.what₂.thetaP μ j (D.what₂.thetaT μ j f) = ((D.what₂.lamP μ j σ : ℝ) : ℂ) • f) ∧
    (D.what₂.isot j σ ≠ ⊥ → 0 < D.what₂.lamP μ j σ)

end Formalism.MainNotions.N

end
