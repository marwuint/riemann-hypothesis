import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.ParConsts

noncomputable section

namespace Formalism.MainNotions.TwistedPlaces

open Formalism.BasicNotions Formalism.MainNotions

def FamilyThinScalesBound {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop := ∃ x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def OrbitValuationBound {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C x0 : ℝ, ∀ x ≥ x0, ∀ i : Fm.Ix x, aux₃ (Fm.L x i) C

def AdmFC {eps : ℝ} (Fm : FamP eps) (C : ℝ) : Prop :=
  ∃ x0 : ℝ, ∀ x ≥ x0, ∀ (hx : Fm.x1 < x) (i : Fm.Ix x), admitted (Fm.L x i) (Fm.params x hx i) C

def AdmF {eps : ℝ} (Fm : FamP eps) : Prop := ∃ C : ℝ, AdmFC Fm C

def KudlaFamilyStatement {eps : ℝ} (Fm : FamP eps) : Prop := AdmF Fm → OrbitValuationBound Fm

def UniformExportStatement (eps : ℝ) : Prop := ∀ Ca : ℝ, ∃ C : ℝ, ∀ Fm : FamP eps, AdmFC Fm Ca → FamilyThinScalesBound Fm C

theorem stmtF_of_stmtU {eps : ℝ} (h : UniformExportStatement eps) (Fm : FamP eps) : KudlaFamilyStatement Fm := by
  rintro ⟨Ca, hA⟩
  obtain ⟨C, hC⟩ := h Ca
  obtain ⟨x0, h0⟩ := hC Fm hA
  exact ⟨C, x0, h0⟩

end Formalism.MainNotions.TwistedPlaces

namespace Formalism.MainNotions.ExportFamilies

end Formalism.MainNotions.ExportFamilies

end
