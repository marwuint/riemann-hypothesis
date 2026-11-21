import Mathlib
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.HodgeWedgeFields.H1CommutesBaseChange

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TensorProduct Opposite MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.CechDR

attribute [local instance] Over.cartesianMonoidalCategory

namespace MainStatements.Hodge.Sh

variable {R : Type} [CommRing R]

section Prod

variable (X Y : Over (Sp R))

section Chart

variable (U : X.left.affineOpens) (V : Y.left.affineOpens)

def prodChart : Spec (CommRingCat.of (Sec X.hom U.1 ⊗[R] Sec Y.hom V.1)) ⟶ (X ⊗ Y).left :=
  (pullbackSpecIso R (Sec X.hom U.1) (Sec Y.hom V.1)).inv ≫
    Limits.pullback.map (spMap (algebraMap R (Sec X.hom U.1))) (spMap (algebraMap R (Sec Y.hom V.1))) X.hom Y.hom
      (affPt X.hom U) (affPt Y.hom V) (𝟙 _) (by rw [Category.comp_id, affPt_w])
      (by rw [Category.comp_id, affPt_w])

instance isOpenImmersion_prodChart : IsOpenImmersion (prodChart X Y U V) := by
  have : IsOpenImmersion (affPt X.hom U) := U.2.isOpenImmersion_fromSpec
  have : IsOpenImmersion (affPt Y.hom V) := V.2.isOpenImmersion_fromSpec
  unfold prodChart
  infer_instance

end Chart

end Prod

end MainStatements.Hodge.Sh
