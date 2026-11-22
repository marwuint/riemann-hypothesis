import Formalism.LocalToGlobal.Columns.ChainLawLev
import Formalism.LocalToGlobal.Columns.ChainLawPhi
import Mathlib
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.Columns.RecLevelSym

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Units

variable {E : Type} [Field E] [NumberField E] {P : HeightOneSpectrum (𝓞 E)} {K : Type} [Field K]

theorem clX_unitV_ne (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hU : IsUnit (redP P a)) : LocE.unitV χ a ≠ 0 := by
  unfold LocE.unitV
  rw [dif_pos hU]
  exact Units.ne_zero _

theorem clX_unitV_one (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) : LocE.unitV χ (1 : E) = 1 := by
  have h1 : redP P (1 : E) = 1 := by
    have := reduction_coe P (1 : 𝓞 E)
    simpa using this
  have hU : IsUnit (redP P (1 : E)) := by rw [h1]; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos hU]
  have : hU.unit = 1 := Units.ext (by simpa using h1)
  rw [this, map_one, Units.val_one]

theorem clX_unitV_inv (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (hu : IntAt P a) (hu' : IntAt P a⁻¹) (h0 : a ≠ 0) :
    LocE.unitV χ a⁻¹ = (LocE.unitV χ a)⁻¹ := by
  have hne := clX_unitV_ne χ (isUnit_reduction_of_integralAt_inv hu hu' h0)
  have hm := unitV_mul_unit χ hu hu' h0 a⁻¹
  rw [inv_mul_cancel₀ h0, clX_unitV_one] at hm
  exact eq_inv_of_mul_eq_one_left hm.symm

end Units

end Formalism.L2.Col
