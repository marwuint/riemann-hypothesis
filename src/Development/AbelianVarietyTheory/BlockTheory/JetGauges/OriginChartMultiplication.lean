import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.DegUnif
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.LawsChart
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CocycleRightZeroThd

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
open scoped TensorProduct

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication

def jetOfSeries {R : Type} [CommRing R] {κ : Type} [Finite κ] (m : ℕ) (f : MvPowerSeries κ R) :
    JetR R κ m :=
  Ideal.Quotient.mk _ (MvPowerSeries.truncTotal (m + 1) f)

def IsOriginChart {R : Type} [CommRing R] (G : Over (Sp R)) [GrpObj G] {d : ℕ}
    (x : ∀ m : ℕ, algOver R (JetR R (Fin d) m) ⟶ G) (F : FGLaw R d) : Prop :=
  (∀ m, algOverHom (jetTruncR R (Fin d) m) ≫ x (m + 1) = x m) ∧
  (∀ m, algOverHom (jetZeroR R (Fin d) m) ≫ x m = toUnit _ ≫ η[G]) ∧
  (∀ (κ : Type) (m : ℕ) (y : algOver R (JetR R κ m) ⟶ G),
    algOverHom (jetZeroR R κ m) ≫ y = toUnit _ ≫ η[G] →
    ∃! ψ : JetR R (Fin d) m →ₐ[R] JetR R κ m,
      (∀ j, jetZeroR R κ m (ψ (zR m j)) = 0) ∧ y = algOverHom ψ ≫ x m) ∧
  (∀ m, ∃ ψ₀ ψ₁ ψ : JetR R (Fin d) m →ₐ[R] JetR R (Fin 2 × Fin d) m,
    (∀ j, ψ₀ (zR m j) = zR m ((0 : Fin 2), j)) ∧ (∀ j, ψ₁ (zR m j) = zR m ((1 : Fin 2), j)) ∧
    (∀ j, ψ (zR m j) = jetOfSeries m (F.F j)) ∧
    lift (algOverHom ψ₀ ≫ x m) (algOverHom ψ₁ ≫ x m) ≫ μ[G] = algOverHom ψ ≫ x m)

end GlobalTheory.IndefiniteRowSideFullHecke.OriginChartMultiplication
