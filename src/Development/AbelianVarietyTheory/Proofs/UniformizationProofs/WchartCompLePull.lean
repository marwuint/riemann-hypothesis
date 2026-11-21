import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.MapsAtLeA
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.CubePullbacks.CubePull
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.LcgLinCombEqProd

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

lemma wchart_comp_le_pull {X X' Y : Scheme.{0}} (L : LB X) {J : Type} [Fintype J]
    (F : J → (X' ⟶ X)) (q : Y ⟶ X') (jN : J → L.ι) :
    LB.wchart L (fun i => q ≫ F i) jN ≤
      LB.wchart (LB.LinComb L F (fun _ => 1)) (fun _ : PUnit => q) (fun _ => jN) :=
  fun _ hy => Set.mem_iInter.2 fun _ => Set.mem_iInter.2 fun i => Set.mem_iInter.1 hy i

end GlobalTheory
