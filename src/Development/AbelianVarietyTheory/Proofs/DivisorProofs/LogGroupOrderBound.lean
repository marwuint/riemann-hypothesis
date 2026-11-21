import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop

noncomputable section

namespace GlobalTheory.CovTop

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem card_GL_zmod_le (r q : ℕ) (hq : q ≠ 0) :
    Nat.card (GL (Fin r) (ZMod q)) ≤ q ^ (r * r) := by
  haveI : NeZero q := ⟨hq⟩
  calc Nat.card (GL (Fin r) (ZMod q)) ≤ Nat.card (Matrix (Fin r) (Fin r) (ZMod q)) :=
        Nat.card_le_card_of_injective (fun u => (u : Matrix (Fin r) (Fin r) (ZMod q))) (fun a b h => Units.ext h)
    _ = q ^ (r * r) := by
        rw [Nat.card_eq_fintype_card]
        show Fintype.card (Fin r → Fin r → ZMod q) = q ^ (r * r)
        rw [Fintype.card_fun, Fintype.card_fun, ZMod.card, Fintype.card_fin, ← pow_mul]

end GlobalTheory.CovTop

end
