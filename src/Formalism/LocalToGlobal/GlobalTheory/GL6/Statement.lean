import Formalism.SharpRestriction.GlobalSchurBounds.ProductFirstZerothParts
import Formalism.LocalToGlobal.HermitianForms.FormsTied

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts Classical NumberField

section Split

variable (D : D7) (u : D.what₂.Word)

def KernelOperatorLatticeInclusions (C : ℝ) : Prop :=
  ∀ w, OverT D u w →
    ∀ i, i < D.R.m →
      ((D.fm u).seenP w = false →
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) ((D.fm u).S (i + 1) w)) ∧
      ((D.fm u).seenP w = true → ∃ BV, IsBfam D u (i + 1) w BV ∧
        Into D u w (fun φ => tpow D u (lossK D u C) • KT D u i φ) ((D.fm u).S i w) (BV Finset.univ)) ∧
      (∃ e1 : ℕ, (e1 : ℝ) ≤ 4 * ∑ τ, (Wt D u τ : ℝ) + C * D.R.f * D.R.N D.R.m ∧
        Into D u w (fun φ => tpow D u e1 • Uprod D u (i + 1) w (KT D u i φ))
          ((D.fm u).S i w) ((D.fm u).S (i + 1) w))

def CongruenceLatticeLengthBound : Prop :=
  ∀ w, OverT D u w →
    Nlam D u w ≤ Sram D u w ∧
    (∃ n : ℕ, len D u w (Sram D u w) (Nlam D u w) = n ∧
      (n : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.R.m * D.duS u * ∑ v ∈ VV D u w,
        ((amax D u : ℝ) / D.R.k + 2 * Wt D u ((D.fm u).tauOf w v) + D.R.k + (D.fm u).bTop ((D.fm u).tauOf w v))))

end Split

end Formalism.L2.GlobalTheoryTheory.LocalLatticeBases

end
