import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisRepWeilJumps

open NumberField IsDedekindDomain Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.HalfTwist

theorem eta_char (D : D7) (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaT w) (D.naut.locG D.naut.etaTinv w) = D.naut.lpUnr w {1} := by
  have hu := D.naut.etaT_unr w
  have hinv := D.naut.etaTinv_def w
  have hd1 : D.naut.lpDim (D.naut.locG D.naut.etaTinv w) = 1 := D.naut.locG_dim _ _
  have hcard : Multiset.card (D.naut.frobEig (D.naut.locG D.naut.etaT w)) = 1 := by
    rw [D.naut.frobEig_card _ hu, D.naut.locG_dim]
  obtain ⟨b, hb⟩ := Multiset.card_eq_one.1 hcard
  have hb0 : b ≠ 0 := by
    have h0 := D.naut.frobEig_ne_zero _ hu
    rw [hb] at h0
    intro hb'
    exact h0 (by simp [hb'])
  have hinvb : D.naut.frobEig (D.naut.locG D.naut.etaTinv w) = {b⁻¹} := by
    rw [hinv.2, hb, Multiset.map_singleton]
  have hunr := D.naut.unr_char _ _ hd1 hu hinv.1
  have hf := D.naut.frobEig_char _ _ b⁻¹ hu hinv.1 hd1 hinvb
  rw [D.naut.unr_eq_lpUnr _ hunr, hf, hb, Multiset.map_singleton, mul_inv_cancel₀ hb0]

theorem eta_inf (D : D7) (hA : SumRepresentations.At.TieAut D.nd D.naut) (τ : D.host.E →+* ℂ) :
    ∃ h : ℂ, D.naut.infG D.naut.etaT τ = {h} ∧ D.naut.infG D.naut.etaTinv τ = {-h} ∧
      (h = 1 / 2 ∨ h = -(1 / 2)) := by
  obtain ⟨h1, h2⟩ := hA.2.1 τ
  rcases h1 with h1 | h1
  · exact ⟨1 / 2, h1, by rw [h2, h1, Multiset.map_singleton], Or.inl rfl⟩
  · exact ⟨-(1 / 2), h1, by rw [h2, h1, Multiset.map_singleton], Or.inr rfl⟩

end GlobalTheory.HalfTwist

