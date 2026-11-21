import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj UpperHalfPlane
open GlobalTheory.CM

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.EllipticFibrePrincipalData

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

instance (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

def IsPrincipalAt {R : Type} [CommRing R] {ω : R} (C : Ell H R ω) (s : R →+* ℂ) : Prop :=
  ∀ (Q : Out.PolAV (Sp ℂ)) (ψ : Q.A.left ⟶ C.P.A.left), IsPolFibre s C.P Q ψ → ∀ u : HolUnif Q.A Q.L Q.g,
    ∃ c : ℂ, c ≠ 0 ∧ PureType.IsQuadLattice u.Λ H.d c

variable {K : Type} [Field K] [NumberField K]

structure IsExp {S : Scheme.{0}} (t : SAB H S) (y : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (ex : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop where
  period : IsPeriod D ty Pe
  add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ Pe.range
  lin : ∀ (a : 𝓞 E) z, ex (fun k => ty k (a : E) * z k) = ex z ≫ t.act.act a
  hol : IsHolTo Set.univ (fun z => (ex z).left)
  diff : ∀ w, ∃! v : epsPt y ⟶ t.G, IsDerivAt0 (fun z => (ex z).left) w v.left
  diff_onto : ∀ v : epsPt y ⟶ t.G, spMap (TrivSqZeroExt.fstHom ℂ ℂ ℂ).toRingHom ≫ v.left = (ex 0).left →
    ∃! w, IsDerivAt0 (fun z => (ex z).left) w v.left
  weil : ∀ (n : ℕ) (a b : D.La) (c : ℂˣ), 0 < n →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / n) →
    Out.WeilIs t.G t.PP.L n (ex ((n : ℂ)⁻¹ • Pe a)) (ex ((n : ℂ)⁻¹ • Pe b)) (unitOn c)

end GlobalTheory.IndefiniteRowSideFullHecke.EllipticFibrePrincipalData
end
