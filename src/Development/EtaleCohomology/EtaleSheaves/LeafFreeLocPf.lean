import Development.EtaleCohomology.EtaleSheaves.LeafChartRing

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC LateralTheory.E.t_E6Cut

namespace LateralTheory.E.LeafFreeLocPf

lemma mapApp (R : Type) [CommRing R] {X Y : PSh} (φ : X ⟶ Y) (V : Scheme.{0}) (z : ((freeP R).obj X).obj (op V)) :
    (((freeP R).map φ).app (op V)).hom z =
      Finsupp.mapDomain (fun x : ULift (X.obj (op V)) => ULift.up (φ.app (op V) x.down)) z := rfl

end LateralTheory.E.LeafFreeLocPf
