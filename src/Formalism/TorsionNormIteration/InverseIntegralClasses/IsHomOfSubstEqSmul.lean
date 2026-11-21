import Formalism.TorsionNormIteration.InvIntegralOfClass
import Formalism.FormalGroupLog.LogDeterminesLaw

noncomputable section

open PowerSeries

namespace Formalism.LT.PadicP

open Formalism.G

theorem coeff_one_subst {R : Type} [CommRing R] (f a : PowerSeries R)
    (hf0 : constantCoeff f = 0) (ha0 : constantCoeff a = 0) :
    coeff 1 (f.subst a) = coeff 1 f * coeff 1 a := by
  have ha : HasSubst a := HasSubst.of_constantCoeff_zero' ha0
  change MvPowerSeries.coeff (Finsupp.single () 1) _ = _
  rw [coeff_subst ha]
  change ∑ᶠ d, coeff d f • coeff 1 (a ^ d) = _
  rw [finsum_eq_single _ 1]
  · rw [pow_one, smul_eq_mul]
  · intro d hd
    obtain ⟨a', rfl⟩ := X_dvd_iff.mpr ha0
    rcases Nat.lt_or_gt_of_ne hd with h | h
    · have h0 : d = 0 := by omega
      subst h0
      rw [pow_zero, coeff_one, if_neg one_ne_zero, smul_zero]
    · rw [mul_pow, coeff_X_pow_mul', if_neg (by omega), smul_zero]

end Formalism.LT.PadicP

namespace Formalism.LT

end Formalism.LT
