import Formalism.WachLatticeTwists.CupProductVanishing.Statement
import Formalism.WachLatticeTwists.CharacterSplitJumps.CharacterJumpProofs.MemAnnih
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.LocDualOrth
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.QuotLen
import Formalism.WachLatticeTwists.LatticeDualFibres.LatticeDualProofs.ExistsBasisOfLattice

variable [hT2Core : Fact ReciprocityTheory.ChartRestriction.T2.Core]

open Formalism.NG (KO annih)
open ReciprocityTheory.Gal Formalism.RepresentationBoundsCohomology.LOC Formalism.RepresentationBoundsCohomology.JT
open ReciprocityTheory.ChartRestriction.T2 (GK PadicCoeff FracTop IsCyc)

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.T2

theorem compat : StatCompat := by
  intro O G VT VT' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ D hc a t
  have h : D.pr (D.q a) t = D.inv (mapH2 (twist D.ε (FractionRing O)) (twist D.ε (KO O)) (toKO O) toKO_cont
      (toKO_equiv D.ε) (cupProductH1H1 D.ρT D.ρT' (twist D.ε (FractionRing O)) D.bT D.contbT D.eqT D.contT' a (D.j' t))) := by
    induction a using Submodule.Quotient.induction_on with
    | H a =>
      induction t using Submodule.Quotient.induction_on with
      | H t => rfl
  rw [h, hc]
  rfl

end Formalism.RepresentationBoundsCohomology.T2
