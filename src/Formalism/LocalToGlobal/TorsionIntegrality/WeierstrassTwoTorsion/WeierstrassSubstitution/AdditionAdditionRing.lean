import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.FlowDouble

open PowerSeries

universe u v

noncomputable section

namespace Formalism.L2.Th1.A

namespace PlusR

abbrev P7 : Type := MvPolynomial (Fin 7) ℤ

abbrev dX : P7 := MvPolynomial.X 3 - MvPolynomial.X 5

abbrev Univ : Type := Localization.Away dX

theorem dX_ne_zero : dX ≠ 0 :=
  sub_ne_zero.mpr fun h => absurd (MvPolynomial.X_injective h) (by decide)

theorem powers_le : Submonoid.powers dX ≤ nonZeroDivisors P7 :=
  powers_le_nonZeroDivisors_of_noZeroDivisors dX_ne_zero

instance : IsDomain Univ := IsLocalization.isDomain_localization powers_le

instance : CharZero Univ :=
  charZero_of_injective_algebraMap (IsLocalization.injective Univ powers_le)

end PlusR

end Formalism.L2.Th1.A
