import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DataRigidTorsionOfDataRigid
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ToStkAInjective

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G.Semi
open scoped CategoryTheory.Obj

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}
variable {D : Datum H} {l : Level H} {c : Coeff l}

def WeilRosatiSt : Prop :=
  ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : Out.PolAV S) (O : Type) [Ring O] [StarRing O] (o : P.OAct O)
    (k : ℕ) (T : Over S) (x y : T ⟶ P.A) (a : O) (c : Γ(T.left, ⊤)ˣ), x ^ k = 1 → y ^ k = 1 →
    (Out.WeilIs P.A P.L k (x ≫ o.act a) y c ↔ Out.WeilIs P.A P.L k x (y ≫ o.act (star a)) c)

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
