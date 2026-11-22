import Formalism.SharpRestriction.GrowthBounds.ScaleEdges.SPtrueHom

noncomputable section

open Finset Classical

namespace Formalism.MainNotions.Pf14

open Formalism.MainNotions.G Formalism.MainNotions.SourceCleaning Formalism.MainNotions.G.WittFrameLocaliserOrders

section Fr

variable {n' r : ℕ} [NeZero n'] {F : Frames n' r} {L₁ N₁ : ℕ}

private theorem fr_lt_fr_of_lt (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l < l') (hl' : l' < r) :
    F.fr j l < F.fr j l' := by
  obtain ⟨-, -, hinc, -⟩ := hV
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_lt hll
  induction m with
  | zero => exact hinc j l (by omega)
  | succ m ih =>
    have h1 := ih (by omega) (by omega)
    have h2 := hinc j (l + m + 1) (by omega)
    show F.fr j l < F.fr j (l + m + 1 + 1)
    exact lt_trans h1 h2

private theorem fr_le_fr_of_le (hV : F.Valid L₁ N₁) (j : ℤ) {l l' : ℕ} (hll : l ≤ l') (hl' : l' < r) :
    F.fr j l ≤ F.fr j l' := by
  rcases Nat.lt_or_eq_of_le hll with h | rfl
  · exact le_of_lt (fr_lt_fr_of_lt hV j h hl')
  · exact le_rfl

theorem fr_le_last (hV : F.Valid L₁ N₁) (j : ℤ) {l : ℕ} (hl : l < r) : F.fr j l ≤ F.fr j (r - 1) := by
  exact fr_le_fr_of_le hV j (by omega) (by omega)

end Fr

end Formalism.MainNotions.Pf14
