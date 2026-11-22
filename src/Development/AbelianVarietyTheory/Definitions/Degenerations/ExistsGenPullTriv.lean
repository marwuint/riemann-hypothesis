import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Definitions.Uniformization.IsCPPullback

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.LN
open GlobalTheory.UU
variable {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {I : Ideal R}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

structure TowerR (I : Ideal R) (P : CP G) (X : Type) [AddCommGroup X] where
  l : ∀ e, Lev I P X e
  tor : ∀ e, TorusCompat (thickTrans R I e) (thickMap R I e G) (l e).Q.i (l (e + 1)).Q.i
  β : ∀ e, (l e).Q.B.left ⟶ (l (e + 1)).Q.B.left
  β_pb : ∀ e, IsCPPullback (l e).D.M (l (e + 1)).D.M (thickTrans R I e) (β e)
  β_q : ∀ e, (l e).Q.q.left ≫ β e = thickMap R I e G ≫ (l (e + 1)).Q.q.left

structure TowerR.Alg {P : CP G} {X : Type} [AddCommGroup X] (t : TowerR I P X) where
  B : Over (Spec (CommRingCat.of R))
  [grp : GrpObj B]
  [comm : IsCommMonObj B]
  isAb : IsAbelianScheme B
  M : CP B
  ample : RelAmple B M.L.L
  b : ∀ e, (t.l e).Q.B.left ⟶ B.left
  b_pb : ∀ e, IsCPPullback (t.l e).D.M M (thick R I e) (b e)
  b_β : ∀ e, t.β e ≫ b (e + 1) = b e
attribute [instance] TowerR.Alg.grp TowerR.Alg.comm

def TowerR.Alg.RepWt {P : CP G} {X : Type} [AddCommGroup X] {t : TowerR I P X} (a : t.Alg) (c : 𝟙_ _ ⟶ a.B) (χ : X) (e : ℕ) : Prop :=
  ∃ u : LB.Gen ((LB.LinComb a.M.L.L (K := Fin 2) ![((toUnit a.B ≫ c) * 𝟙 a.B).left, 𝟙 a.B.left] ![-1, 1]).pull
      ((t.l e).Q.q.left ≫ a.b e)), u.IsGen ∧ ∀ j, IsWt (t.l e).Q.i _ (u.s j).val χ

open GlobalTheory.SplitTorus

end GlobalTheory.LN
end
