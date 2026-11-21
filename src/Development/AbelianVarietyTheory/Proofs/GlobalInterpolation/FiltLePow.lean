import Mathlib

open MvPowerSeries

namespace GlobalTheory.FiltrationMultiplicative

section

variable {O : Type} [CommRing O] [IsLocalRing O]

def IsFirst {a : ℕ} (m : Fin a →₀ ℕ) (i : Fin a) : Prop := m i ≠ 0 ∧ ∀ j, j < i → m j = 0

open Classical in

noncomputable def part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) :
    MvPowerSeries (Fin a) O :=
  fun q => if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0

open Classical in
theorem coeff_part {a : ℕ} (f : MvPowerSeries (Fin a) O) (i : Fin a) (q : Fin a →₀ ℕ) :
    coeff q (part f i) =
      if IsFirst (q + Finsupp.single i 1) i then coeff (q + Finsupp.single i 1) f else 0 :=
  rfl

end

end GlobalTheory.FiltrationMultiplicative
