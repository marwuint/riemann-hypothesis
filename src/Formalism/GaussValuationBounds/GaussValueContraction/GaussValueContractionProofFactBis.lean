import Formalism.GaussValuationBounds.Statement
import Formalism.WindowSums.PowerSeriesRelationList

noncomputable section

namespace Formalism.NOK

open Polynomial

theorem padicInt_valuation_unit (ℓ : ℕ) [Fact ℓ.Prime] (u : ℤ_[ℓ]ˣ) :
    (u : ℤ_[ℓ]).valuation = 0 := by
  have h := PadicInt.valuation_mul (Units.ne_zero u) (Units.ne_zero u⁻¹)
  rw [Units.mul_inv, PadicInt.valuation_one] at h
  omega

theorem cjExist_proof : CjExist := by
  intro ℓ _ hℓ χ hχ
  have hZ := Formalism.WindowSums.arc_ZpowVal ℓ χ 1 le_rfl (fun h => absurd h hℓ) hχ
  have hℓ0 : (ℓ : ℤ_[ℓ]) ≠ 0 := by exact_mod_cast (Fact.out : ℓ.Prime).ne_zero
  have hdvd : ∀ j : ℤ, (ℓ : ℤ_[ℓ]) ∣ ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    by_cases hj : j = 0
    · subst hj
      simp
    · obtain ⟨hne, hv⟩ := hZ (-j) (neg_ne_zero.2 hj)
      rw [PadicInt.unitCoeff_spec hne]
      exact Dvd.dvd.mul_left (dvd_pow_self _ (by rw [hv]; omega)) _
  choose d hd using hdvd
  have hc1 : ∀ j, -(ℓ : ℤ_[ℓ]) * (-d j) = ((χ ^ (-j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1 := by
    intro j
    rw [hd j]
    ring
  have key : ∀ j j' : ℤ, j ≠ j' → -d j' - -d j ≠ 0 ∧
      PadicInt.valuation (-d j' - -d j) = padicValInt ℓ (j' - j) := by
    intro j j' hjj
    have hid : χ ^ (-j) = χ ^ (-j') * χ ^ (j' - j) := by
      rw [← zpow_add]
      congr 1
      ring
    have hkey : (ℓ : ℤ_[ℓ]) ^ 1 * (-d j' - -d j) =
        ((χ ^ (-j') : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * (((χ ^ (j' - j) : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) - 1) := by
      have e1 := hd j
      have e2 := hd j'
      rw [hid, Units.val_mul] at e1
      linear_combination e2 - e1
    obtain ⟨hne, hv⟩ := hZ (j' - j) (sub_ne_zero.2 (Ne.symm hjj))
    have hw : -d j' - -d j ≠ 0 := by
      intro h
      rw [h, mul_zero] at hkey
      exact mul_ne_zero (Units.ne_zero _) hne hkey.symm
    refine ⟨hw, ?_⟩
    have h1 := PadicInt.valuation_p_pow_mul 1 (-d j' - -d j) hw
    rw [hkey, PadicInt.valuation_mul (Units.ne_zero _) hne, padicInt_valuation_unit, hv] at h1
    omega
  refine ⟨fun j => -d j, hc1, ?_, fun j j' h => key j' j (Ne.symm h)⟩
  have h0 : (ℓ : ℤ_[ℓ]) * d 0 = 0 := by
    rw [← hd 0]
    simp
  show -d 0 = 0
  rw [neg_eq_zero]
  exact (mul_eq_zero.1 h0).resolve_left hℓ0

end Formalism.NOK
