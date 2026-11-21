import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

section Iso

variable {S S' : Scheme.{0}} {G' : Over S'} {G : Over S} [GrpObj G'] [IsCommMonObj G']
  [GrpObj G] [IsCommMonObj G]

structure IsRigIso (m : CubeMap G' G) (L' : RigLB G') (L : RigLB G)
    (w : LB.Iso L'.L (L.L.pull m.F)) : Prop where
  gen : w.IsGen
  rig : LB.Gen.Maps (LB.linCombIso w (K := PUnit) (fun _ => eSec G') (fun _ => 1)) L'.rig
    (m.rigPull L.L L.rig)

end Iso

section Torus

variable {S : Scheme.{0}} {X : Type} [AddCommGroup X] {G : Over S} [GrpObj G]

def charV (χ : X) {T : Over S} (z : T.left) (t : T ⟶ splitTorus S X) : (T.left.presheaf.stalk z)ˣ :=
  gm t.left z ⊤ (charUnit S X χ)

variable {B : Over S} [GrpObj B]

end Torus

end GlobalTheory.IndefiniteRowSideFullHecke.CubicalSymmetricTriv
