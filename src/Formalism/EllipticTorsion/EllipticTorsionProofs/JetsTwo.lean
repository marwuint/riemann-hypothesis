import Formalism.EllipticTorsion.JetsCube
import Formalism.FormalGroupLog.FormalGroupLogProofs.ConstantCoeffSubstOfZero

universe u

noncomputable section

namespace Formalism.ELL.FormalGroupQuadraticJets

open Formalism.G.LogCR

variable {K : Type*} [CommRing K]

def ccd (i : Fin 2) (H : MvPowerSeries (Fin 2) K) : K :=
  MvPowerSeries.constantCoeff (MvPowerSeries.pderiv K i H)

theorem hv {x y : MvPowerSeries (Fin 2) K} (hx : MvPowerSeries.constantCoeff x = 0)
    (hy : MvPowerSeries.constantCoeff y = 0) :
    ∀ j, MvPowerSeries.constantCoeff (![x, y] j) = 0 := by
  intro j
  fin_cases j <;> simp [hx, hy]

theorem ccd_F (F : MvPowerSeries (Fin 2) K) {x y : MvPowerSeries (Fin 2) K}
    (hx : MvPowerSeries.constantCoeff x = 0) (hy : MvPowerSeries.constantCoeff y = 0)
    (i : Fin 2) :
    ccd i (F.subst ![x, y]) = ccd 0 F * ccd i x + ccd 1 F * ccd i y := by
  unfold ccd
  rw [pderiv_subst (hv hx hy), map_sum, Fin.sum_univ_two]
  simp only [map_mul, Formalism.G.LogP.constantCoeff_subst_of_zero _ (hv hx hy), Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons]

theorem ccd_single (F : MvPowerSeries (Fin 2) K) (i : Fin 2) :
    ccd i F = MvPowerSeries.coeff (Finsupp.single i 1) F := by
  unfold ccd
  rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
  simp

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL.FormalGroupQuadraticJets

end Formalism.ELL.FormalGroupQuadraticJets

namespace Formalism.ELL

end Formalism.ELL
