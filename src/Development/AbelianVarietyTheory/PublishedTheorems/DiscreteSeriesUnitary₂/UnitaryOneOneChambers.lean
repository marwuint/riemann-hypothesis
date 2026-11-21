import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.SubmatrixMemUJsetIff
import Development.AbelianVarietyTheory.Proofs.HeightProofs.RhoCompactTwiceEqOfSignBlockOrdered

open Formalism.MainNotions.S MeasureTheory Matrix
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.FormalDegree.Model

def cst (n : ℕ) (s : Bool) : ℝ := ((Formalism.REAL.muG (fun _ : Fin n => s)).real Set.univ)⁻¹

theorem isFdeg_unique {n : ℕ} {ε : Fin n → Bool} {μ : Measure (Formalism.REAL.UJ ε)} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [Nontrivial H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {d d' : ℝ}
    (h : IsFdeg μ σ d) (h' : IsFdeg μ σ d') : d = d' := by
  obtain ⟨e, he⟩ := exists_ne (0 : H)
  have h1 := (h.2 e e e e).2.symm.trans (h'.2 e e e e).2
  have h2 : ⟪e, e⟫_ℂ ≠ 0 := inner_self_ne_zero.2 he
  have hd : (d : ℂ) ≠ 0 := by exact_mod_cast h.1.ne'
  have hd' : (d' : ℂ) ≠ 0 := by exact_mod_cast h'.1.ne'
  rw [div_eq_div_iff hd hd'] at h1
  exact_mod_cast (mul_left_cancel₀ (mul_ne_zero h2 h2) h1).symm

theorem ratio (hHC : HarishChandra) {n : ℕ} {ε : Fin n → Bool} {lam lam' : Fin n → ℝ}
    (hl : Formalism.QuantumDeterminants.IsHCParam lam) (hl' : Formalism.QuantumDeterminants.IsHCParam lam')
    {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}
    (h : IsDS ε lam σ) (h' : IsDS ε lam' σ') {d d' : ℝ}
    (hd : IsFdeg (Formalism.REAL.muG ε) σ d) (hd' : IsFdeg (Formalism.REAL.muG ε) σ' d') :
    d * Formalism.QuantumDeterminants.fdegHC lam' = d' * Formalism.QuantumDeterminants.fdegHC lam := by
  obtain ⟨c, -, hc⟩ := hHC.chamber n ε
  have := h.2.1
  have := h'.2.1
  rw [isFdeg_unique hd (hc lam hl H σ h), isFdeg_unique hd' (hc lam' hl' H' σ' h')]
  ring

end GlobalTheory.FormalDegree.Model
