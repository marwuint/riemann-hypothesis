import Mathlib

namespace GlobalTheory.PowerSeriesCoeffSum

open MvPowerSeries Finsupp

variable {O : Type} [CommRing O] {a : ℕ}

noncomputable def part (f : MvPowerSeries (Fin a) O) (i : Fin a) : MvPowerSeries (Fin a) O :=
  fun e => if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0

lemma coeff_part (f : MvPowerSeries (Fin a) O) (i : Fin a) (e : Fin a →₀ ℕ) :
    coeff e (part f i) = if (∀ j < i, e j = 0) then coeff (e + single i 1) f else 0 := rfl

end GlobalTheory.PowerSeriesCoeffSum
