import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsPolAVSectionInverseImage

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.LieHt
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.MBLow

def IsPow8 {S : Scheme.{0}} (P P₈ : PolAV S) (d : ℕ) (pr : Fin 8 → (P₈.A ⟶ P.A)) (inc : P.A ⟶ P₈.A) : Prop :=
  (∀ u, IsMonHom (pr u)) ∧ IsMonHom inc ∧ (∀ (T : Over S) (y : Fin 8 → (T ⟶ P.A)), ∃! x : T ⟶ P₈.A, ∀ u, x ≫ pr u = y u) ∧
    (∀ u, inc ≫ pr u = if u = 0 then 𝟙 P.A else 1) ∧ LBIso (P₈.L.pull inc.left) (lbPow P.L d)

end GlobalTheory.MBLow

end
