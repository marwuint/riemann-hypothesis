import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifPowOf3
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigIsoCongr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsMonHomOfMul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExistsZeroGt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.MemFinsetInf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.TangentLinearity.ESecStruct
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.CoordLinear

open Geo.Tor

theorem fn_eq_of_levels {R : Type} [CommRing R] (I : Ideal R) [IsHausdorff I R]
    (W : (Spec (CommRingCat.of R)).Opens) (hW : W = ⊤) (a b : Γ(Spec (CommRingCat.of R), W))
    (h : ∀ e, ((thick R I e).app W).hom a = ((thick R I e).app W).hom b) : a = b := by
  subst hW
  apply (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of R)).hom).1
  have key : ∀ (e : ℕ) (c : Γ(Spec (CommRingCat.of R), ⊤)),
      Ideal.Quotient.mk (I ^ (e + 1)) ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom c) =
        (Scheme.ΓSpecIso (CommRingCat.of (R ⧸ I ^ (e + 1)))).hom.hom (((thick R I e).app ⊤).hom c) := fun e c =>
    (congrArg (fun q => q.hom c)
      (Scheme.ΓSpecIso_naturality (CommRingCat.ofHom (Ideal.Quotient.mk (I ^ (e + 1)))))).symm
  have := IsHausdorff.StrictMono.funext' I (a := fun n => n + 1) (strictMono_id.add_const 1)
    (f := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom a)
    (g := fun _ : Unit => (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom b)
    (fun n _ => (key n a).trans ((congrArg _ (h n)).trans (key n b).symm))
  exact congrFun this ()

end GlobalTheory.CoordLinear
