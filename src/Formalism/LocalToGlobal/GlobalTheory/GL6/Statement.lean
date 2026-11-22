import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Split

variable (D : D7) (u : D.what₂.Word)

def CongruenceLatticeLengthBound : Prop :=
  ∀ w, OverT D u w →
    Nlam D u w ≤ Sram D u w ∧
    (∃ n : ℕ, len D u w (Sram D u w) (Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ VV D u w,
        ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v))))

end Split

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
