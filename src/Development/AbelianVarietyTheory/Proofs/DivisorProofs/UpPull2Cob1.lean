import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FormalGroupLawCoboundaryTwoCoboundaryOne

set_option autoImplicit false

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog

namespace GlobalTheory

namespace Katz

namespace ExtCoeff

variable {O E : Type} [CommRing O] [CommRing E] {d : ℕ}

theorem hasSubst_XL : HasSubst (fun i : Fin d => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem hasSubst_XR : HasSubst (fun i : Fin d => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) O)) :=
  hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _

theorem map_inL (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inL f) = inL (map h f) := by
  unfold inL
  rw [map_subst hasSubst_XL]
  congr 1
  funext i
  exact map_X h _

theorem map_inR (h : O →+* E) (f : MvPowerSeries (Fin d) O) : map h (inR f) = inR (map h f) := by
  unfold inR
  rw [map_subst hasSubst_XR]
  congr 1
  funext i
  exact map_X h _

theorem map_formalGroupLawCoboundaryOne_eq (h : O →+* E) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) O)
    (s : MvPowerSeries (Fin d) O) (hμ : ∀ i, constantCoeff (μ i) = 0) :
    cob1 (fun i => map h (μ i)) (map h s) = map h (cob1 μ s) := by
  unfold cob1
  rw [map_sub, map_sub, map_subst (hasSubst_of_constantCoeff_zero hμ), map_inL, map_inR]

end ExtCoeff

end Katz

end GlobalTheory
