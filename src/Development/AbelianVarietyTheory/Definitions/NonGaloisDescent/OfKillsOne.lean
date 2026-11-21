import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RoundDown

noncomputable section

open PowerSeries

namespace GlobalTheory.NB

variable {l : ℕ} {O : Type} [CommRing O] [IsDomain O] {R : Fr l O} {n r₁ r : ℕ}

def Fr.InFF (R : Fr l O) (m : ℕ) (up : ℕ → Fin R.e → Bool) (b : ℕ → Fin R.e → ℕ) (Sn : ℕ)
    (f : R.EE) : Prop :=
  (∃ a : O⟦X⟧, R.ι (∏ s ∈ Finset.range m, ∏ τ, if up s τ then R.pt s τ ^ b s τ else 1) * f = R.ι a) ∧
    ∀ s < m, ∀ τ, up s τ = false → R.ConstMod (R.pt s τ) ((b s τ : ℤ) + Sn) f

structure Typed {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Fin R.e → Bool)
    (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  good : F.Good
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m

structure TypedOnto {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S)
    (up : ZMod n → Fin R.e → Bool) (b : ZMod n → Fin R.e → ℕ) (Sn η m h : ℕ) : Prop where
  onto : F.Onto
  jumps : ∀ i τ, S₁.JumpsIn i τ (win (up i τ) (b i τ) Sn η)
  size : ∀ i τ, η < b i τ
  le_h : ∀ i τ, b i τ + Sn ≤ h
  low : ∀ i τ, S.count i τ (-(η : ℤ)) η ≤ m

structure BSet {S₁ : Sys R n r₁} {S : Sys R n r} (F : Hom S₁ S) (up : ZMod n → Bool)
    (sz : ZMod n → ℕ) (b w Sn η m h : ℕ) : Prop where
  isA : R.IsA
  l_ge : 11 ≤ l
  n_pos : 0 < n
  typed : TypedOnto F (fun i _ => up i) (fun i _ => sz i) Sn η m h
  w_pos : 1 ≤ w
  small : 20 * w ≤ b ∧ 20 * η ≤ b ∧ 20 * Sn ≤ b
  thick_or : ∀ i, (b ≤ sz i ∧ sz i ≤ b + η) ∨ sz i ≤ w
  some_thin : ∃ i, sz i ≤ w
  h_def : ((∃ i, b ≤ sz i) → h = b + η + Sn) ∧ ((∀ i, sz i ≤ w) → h = w + Sn)

section Rel

variable {S₁ : Sys R n r₁} {S : Sys R n r} {F : Hom S₁ S}

omit [IsDomain O] in

theorem Hom.Kills.of_dvd {i : ZMod n} {f g : O⟦X⟧} (h : F.Kills i f) (hfg : f ∣ g) :
    F.Kills i g := by
  obtain ⟨c, rfl⟩ := hfg
  intro y hy
  obtain ⟨x, hx, e⟩ := h (c • y) (Submodule.smul_mem _ _ hy)
  exact ⟨x, hx, by rw [e, smul_smul]⟩

end Rel

end GlobalTheory.NB
