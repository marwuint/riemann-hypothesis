import Mathlib
import Formalism.LocalToGlobal.ProjectiveLattices.IntAllProofFree
import Formalism.LocalToGlobal.ProjectiveLattices.IntFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.WtFieldPfA

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.ReframeClauses

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open IsDedekindDomain
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open Formalism.L2.PjFree (FrBaseChg ReFrame XoNumPt TanLin SClause IntRebase)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
variable {Xo : Moduli Dw l} {c : Coeff l}

section Comb

variable {S S' : Type} [CommRing S] [CommRing S']

theorem isTanAt_of_isCombAt {x : Sp S ⟶ Xo.X} {m : ℕ} {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)}
    (hv : ∀ j, IsTanAt x (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsTanAt x w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_tan x _ (fun j => hv j) a

theorem isEigAt_of_isCombAt [Algebra c.F S] {x : Sp S ⟶ Xo.X} {m : ℕ}
    {v : Fin m → (Sp (DualNumber S) ⟶ Xo.univ.t.G.left)} (hv : ∀ j, IsTanAt x (v j)) {τ : E →+* ℂ}
    (he : ∀ j, IsEigAt c τ (v j)) {a : Fin m → S} {w : Sp (DualNumber S) ⟶ Xo.univ.t.G.left}
    (h : IsCombAt x v a w) : IsEigAt c τ w := by
  rw [← (ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_isComb_iff x v hv a w).1 h]
  exact ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_comb_eig x c τ (fun j => ReciprocityTheory.ChartRestriction.G.PullbackSections.wtfA_lt x (v j) (hv j)) he a

end Comb

variable (Xo c)

variable {Xo c}

end GlobalTheory.ReframeClauses
