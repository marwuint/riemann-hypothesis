import Formalism.LocalRingCardinality.DataKerI
import Formalism.LocalRingCardinality.SpanPowerMembership.ExistsHomOfBasis

open Formalism.MainNotions.G Formalism.BasicNotions NumberField

noncomputable section

namespace Formalism.BasicNotions.Examples₂

structure EntPl (D : D7) where
  lam : ∀ w : D.what₂.places.Pl, (algebraicClosure ℚ ℂ) →+* ℂ_[D.what₂.places.resChar w]
  iL : ∀ w : D.what₂.places.Pl, D.what₂.LL →+* ℂ_[D.what₂.places.resChar w]
  iL_lam : ∀ w x, iL w x = lamV (lam w) (D.what₂.embLL x)
  iL_lam' : ∀ w x (hx : D.what₂.embLL x ∈ algebraicClosure ℚ ℂ), iL w x = lam w ⟨D.what₂.embLL x, hx⟩
  iL_int : ∀ w x, x ∈ intW D.what₂.places w ↔ ‖iL w x‖ ≤ 1

theorem entPl_nonempty (D : D7) : Nonempty (EntPl D) := by
  choose lam iL h1 h2 using fun w => exists_placeEmb D w
  exact ⟨⟨lam, iL, fun w x => by
    obtain ⟨hx, e⟩ := h1 w x
    rw [lamV, dif_pos hx, e], fun w x _ => (h1 w x).choose_spec, h2⟩⟩

end Formalism.BasicNotions.Examples₂
