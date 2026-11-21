import Formalism.LocalRingCardinality.DataNChoice

noncomputable section

namespace Formalism.MainNotions.Inhab

open Formalism.BasicNotions NumberField IsDedekindDomain IsLocalRing

section Rec

variable (D : D7)

theorem resChar_mem (w : D.what₂.places.Pl) : ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) ∈ (D.plEq w).asIdeal := by
  have h1 := D.what₂.places.val_resChar w
  have hne : ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    Nat.cast_ne_zero.2 (D.what₂.places.resChar_prime w).ne_zero
  rw [D.val_eq w _ hne, Formalism.BasicNotions.vAdd] at h1
  have h2 := WithTop.coe_injective h1
  have hv0 : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) ≠ 0 :=
    (Valuation.ne_zero_iff _).2 hne
  obtain ⟨n, hn⟩ : ∃ n : ℤ,
      (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) = WithZero.exp n :=
    ⟨_, (WithZero.exp_log hv0).symm⟩
  rw [hn, WithZero.log_exp] at h2
  have hpos := D.what₂.places.ramIdx_pos w
  have hlt : (D.plEq w).valuation D.what₂.LL ((D.what₂.places.resChar w : ℕ) : D.what₂.LL) < 1 := by
    rw [hn, ← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  rw [← IsDedekindDomain.HeightOneSpectrum.intValuation_lt_one_iff_mem]
  have e : (D.plEq w).valuation D.what₂.LL
      (algebraMap (𝓞 D.what₂.LL) D.what₂.LL ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL)) =
      (D.plEq w).intValuation ((D.what₂.places.resChar w : ℕ) : 𝓞 D.what₂.LL) :=
    IsDedekindDomain.HeightOneSpectrum.valuation_of_algebraMap _ _
  rw [← e, map_natCast]
  exact hlt

end Rec

end Formalism.MainNotions.Inhab

end
