import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmpNaturality
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsClosedImmersionIffPullRatio

set_option autoImplicit false

noncomputable section

open CategoryTheory Limits AlgebraicGeometry TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.VB GlobalTheory.LineQuot
open GlobalTheory.LB (resG_resG resG_self fun_ext_of_cover exists_fun_of_cover)
open GlobalTheory.Twist (resM resM_resM resM_self resM_smul app_resM sec_ext_of_cover exists_sec_of_cover)

namespace GlobalTheory.LineQuot.ExMap

variable {T : Scheme.{0}} {L Q : T.Modules}

def IsRatio (a b : L ⟶ Q) (V : T.Opens) (c : Γ(T, V)) : Prop :=
  ∀ (V' : T.Opens) (h : V' ≤ V) (t : Γ(L, V')), b.app V' t = resG T h c • a.app V' t

theorem IsRatio.res {a b : L ⟶ Q} {V : T.Opens} {c : Γ(T, V)} (hc : IsRatio a b V c) {W : T.Opens}
    (h : W ≤ V) : IsRatio a b W (resG T h c) := fun V' h' t => by
  rw [resG_resG]; exact hc V' _ t

end GlobalTheory.LineQuot.ExMap

namespace GlobalTheory.LineQuot.ExMap

end GlobalTheory.LineQuot.ExMap

