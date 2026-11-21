import Formalism.LocalToGlobal.Columns.ChainTopTilQ
import Formalism.LocalToGlobal.Columns.ChainLawXi
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.TopLawQ
import Formalism.LocalToGlobal.Columns.BaseLemmas

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Gen

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem tqk_unitV_one {K : Type} [Field K] (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a : E} (h : redP P a = 1) : LocE.unitV χ a = 1 := by
  have hU : IsUnit (redP P a) := by rw [h]; exact isUnit_one
  unfold LocE.unitV
  rw [dif_pos hU]
  have : hU.unit = 1 := Units.ext (by rw [IsUnit.unit_spec, h]; rfl)
  rw [this, map_one, Units.val_one]

end Gen

end Formalism.L2.Col
