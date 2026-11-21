import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.GeometricLemmaFiltration
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivOfRangeEq
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeometricLemmaCellOneBlockSwapEquiv
open GlobalTheory.PRep GlobalTheory.SmGL Matrix GlobalTheory.SplitWeil
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.DiagCell

theorem mem_parab_of_single {R : Type} [CommRing R] {β : Type} [LinearOrder β] {n : β → ℕ} {t : Type}
    [Fintype t] [DecidableEq t]
    (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β) (h0 : ∀ j, j ≠ a₀ → n j = 0) (x : GL t R) :
    x ∈ parab R e := by
  refine mem_parab_iff.2 fun a b i j hab => ?_
  by_cases ha : a = a₀
  · have hb : b ≠ a₀ := fun e => by rw [e, ha] at hab; exact lt_irrefl _ hab
    exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

theorem eq_one_of_mem_unipRad_single {R : Type} [CommRing R] {β : Type} [Fintype β] [LinearOrder β]
    {n : β → ℕ} {t : Type} [Fintype t] [DecidableEq t] (e : (Σ j, Fin (n j)) ≃ t) (a₀ : β)
    (h0 : ∀ j, j ≠ a₀ → n j = 0) {g : GL t R} (hg : g ∈ unipRad R e) : g = 1 := by
  obtain ⟨-, h2⟩ := mem_unipRad.1 hg
  refine Units.ext (Matrix.ext fun x y => ?_)
  obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective x
  obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective y
  by_cases ha : a = a₀
  · by_cases hb : b = a₀
    · obtain rfl : b = a := hb.trans ha.symm
      rw [h2 b i j]
      simp [Matrix.one_apply]
    · exact absurd j.2 (by have := j.2; have := h0 b hb; omega)
  · exact absurd i.2 (by have := i.2; have := h0 a ha; omega)

end GlobalTheory.DiagCell

namespace GlobalTheory.DiagCell

end GlobalTheory.DiagCell
