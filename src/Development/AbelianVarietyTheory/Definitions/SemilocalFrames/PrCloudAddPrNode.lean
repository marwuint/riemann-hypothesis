import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.SubsingletonIdxZero

open Matrix MeasureTheory Finset Formalism.QuantumDeterminants Formalism.MainNotions.S
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.Mom

variable {k r : ℕ}

def Setup (k r : ℕ) (c Ch : ℝ) (P : Mat k r) (lam : Fin (2 * r + k + 1) → ℝ) (bv h q : ℝ)
    (R : (Fin (2 * r + k + 1) → ℝ) → HRep k r) : Prop :=
  IsCayleyU k r (sgnCN k r) P ∧ IsShape k r lam bv ∧ IsRange k r lam c h q ∧
    Ch * (2 * r + 2 : ℝ) ^ (9 / 2 : ℝ) *
      (3 * (r + 1) * ((2 * r + k + 1 : ℕ) : ℝ) ^ 2 + ((2 * r + k + 1 : ℕ) : ℝ) ^ 3) ≤ h ∧
    ∀ μ, InPP lam q μ → (R μ).IsDSAt P μ

structure Flag (k r : ℕ) where
  z : Fin (2 * r + k + 1) → ℂ
  u : Fin k → ℝ
  W : Type
  [nG : NormedAddCommGroup W]
  [iP : InnerProductSpace ℂ W]
  π : Mat k r → (W →L[ℂ] W)
  cψ : ℂ
  μG : Measure (Mt k r)
  μS : Measure (Mt k r)
  ν : Measure (Mt k r)

attribute [instance] Flag.nG Flag.iP

theorem InPP.mono {n : ℕ} {lam μ : Fin n → ℝ} {s t : ℝ} (h : InPP lam s μ) (hst : s ≤ t) : InPP lam t μ :=
  ⟨h.1, h.2.trans hst⟩

section Conseq

variable {c Ch Cg C₀ bv h q : ℝ} {P : Mat k r} {lam μ : Fin (2 * r + k + 1) → ℝ}
  {R : (Fin (2 * r + k + 1) → ℝ) → HRep k r}

theorem IsRange.mono {q' : ℝ} (hr : IsRange k r lam c h q') (hq : q ≤ q') : IsRange k r lam c h q := by
  have h0 : 100 * max 1 c * q ≤ 100 * max 1 c * q' :=
    mul_le_mul_of_nonneg_left hq (by linarith [le_max_left 1 c])
  exact ⟨hr.1, hr.2.1, (mul_le_mul_of_nonneg_right h0 (Real.sqrt_nonneg _)).trans hr.2.2.1,
    fun i j hij hj => h0.trans (hr.2.2.2 i j hij hj)⟩

theorem Setup.mono {q' : ℝ} (hS : Setup k r c Ch P lam bv h q' R) (hq : q ≤ q') : Setup k r c Ch P lam bv h q R :=
  ⟨hS.1, hS.2.1, hS.2.2.1.mono hq, hS.2.2.2.1, fun μ hμ => hS.2.2.2.2 μ (hμ.mono hq)⟩

namespace Standing

end Standing

end Conseq

end GlobalTheory.Mom
