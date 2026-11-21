import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PlaceDivisors.StChartFH
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.CubicalStructures.CubicalPullBaseChangeSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.IsFormalGroupLawOfChartOfJetChart

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CubeFib

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open ReciprocityTheory.ChartRestriction.G.Pdiv.ChartF
open scoped BigOperators

attribute [local instance] Over.cartesianMonoidalCategory

structure Fib (k : Type) [Field k] where
  G : Over (Sp k)
  [grp : GrpObj G]
  [comm : IsCommMonObj G]
  smooth : Smooth G.hom
  L : RigLB G
  cub : CubicalStr G L
  P : PolAV (Sp k)
  rig : LB.Gen (P.L.pull (eSec P.A))
  rig_gen : rig.IsGen
  cubB : CubicalStr P.A ⟨P.L, rig, P.isLB, rig_gen⟩
  q : G ⟶ P.A
  [q_hom : IsMonHom q]
  q_flat : Flat q.left
  q_surj : Surjective q.left
  q_affine : IsAffineHom q.left
  X : Type
  [addX : AddCommGroup X]
  [freeX : Module.Free ℤ X]
  [finX : Module.Finite ℤ X]
  i : splitTorus (Sp k) X ⟶ G
  i_hom : IsMonHom i
  isKernel : IsPullback i (toUnit _) q (η[P.A])
  pull : (CubeMap.ofHom q).IsPullCubical cub cubB

attribute [instance] Fib.grp Fib.comm Fib.q_hom Fib.addX Fib.freeX Fib.finX

end GlobalTheory.CubeFib
