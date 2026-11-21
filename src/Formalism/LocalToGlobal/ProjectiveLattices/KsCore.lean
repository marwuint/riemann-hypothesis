import Formalism.LocalToGlobal.ProjectiveLattices.XcLat
import Formalism.LocalToGlobal.ProjectiveLattices.ThClassPins

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions

namespace KsCore

variable {D : D7} (T : Core D)

abbrev WK (j : ℕ) (κ : WeightFamilies.Wt D j) : Submodule T.Q.c.F (T.R j) := T.C j κ

def MK (j : ℕ) (κ : WeightFamilies.Wt D j) :=
  latOf (T.C j κ) (T.Vs j) (fun la => isVal_valSet la)

variable {G : Type} [Group G]

def KeepsCu (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) : Prop :=
  ∀ g, ∀ f ∈ T.C j κ, actLev (Xo := T.Q.Xo j) T.Q.c lev g f ∈ T.C j κ

open Classical in

def rhoGeo (j : ℕ) (κ : WeightFamilies.Wt D j)
    (lev : G → ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La) × ((T.Q.Dw j).La →ₗ[𝓞 D.host.E] (T.Q.Dw j).La)) :
    G →* Module.End T.Q.c.F (WK T j κ) :=
  if h : ActLev (Xo := T.Q.Xo j) T.Q.c lev ∧ KeepsCu T j κ lev then
    { toFun := fun g => (actLev (Xo := T.Q.Xo j) T.Q.c lev g).restrict (h.2 g)
      map_one' := by
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_one _ _ _ h.1.total h.1.func h.1.one (cusp_le_sec _ _ _ _ _ f.2).1
      map_mul' := by
        intro g g'
        apply LinearMap.ext
        intro f
        apply Subtype.ext
        exact actL_mul _ _ _ h.1.total h.1.func h.1.mul g g' (cusp_le_sec _ _ _ _ _ f.2).1 }
  else 1

end KsCore

end Formalism.L2.Pj
