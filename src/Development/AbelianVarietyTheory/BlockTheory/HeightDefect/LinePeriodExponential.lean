import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CM
open scoped CategoryTheory.Obj

noncomputable section
namespace GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

instance factPrime (H : Host E) : Fact H.d.Prime := ⟨H.d_prime⟩

variable {H : Host E}

def HasPeriod {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} (C : Ell H (𝓞 M) ω) (x : ℝ) : Prop :=
  ∃ n : (M →+* ℂ) → ℝ, (∀ s, 0 < n s ∧ ∀ r, IsLieNormSq C.P C.v (s.comp (algebraMap (𝓞 M) M)) r ↔ r = n s) ∧
    x = -meanLog M n

theorem HasPeriod.unique {M : Type} [Field M] [NumberField M] {ω : 𝓞 M} {C : Ell H (𝓞 M) ω} {x y : ℝ}
    (hx : HasPeriod C x) (hy : HasPeriod C y) : x = y := by
  obtain ⟨n, hn, rfl⟩ := hx
  obtain ⟨n', hn', rfl⟩ := hy
  rw [show n = n' from funext fun s => ((hn' s).2 _).1 (((hn s).2 _).2 rfl)]

structure IsExp {S : Scheme.{0}} (t : SAB H S) (y : Sp ℂ ⟶ S) (D : Datum H) {g : ℕ} (ty : Fin g → (E →+* ℂ))
    (Pe : D.La →+ (Fin g → ℂ)) (ex : (Fin g → ℂ) → (Over.mk y ⟶ t.G)) : Prop where
  period : IsPeriod D ty Pe
  add : ∀ z w, ex (z + w) = ex z * ex w
  onto : Function.Surjective ex
  ker : ∀ z, ex z = 1 ↔ z ∈ Pe.range
  lin : ∀ (a : 𝓞 E) z, ex (fun k => ty k (a : E) * z k) = ex z ≫ t.act.act a
  hol : IsHolTo Set.univ fun z => (ex z).left
  weil : ∀ (k : ℕ) (a b : D.La) (c : ℂˣ), 0 < k →
    (c : ℂ) = Complex.exp (-(2 * Real.pi * Complex.I) * (D.EF a b : ℂ) / k) →
    Out.WeilIs t.G t.PP.L k (ex ((k : ℂ)⁻¹ • Pe a)) (ex ((k : ℂ)⁻¹ • Pe b)) (unitOn c)

def typeVal (H : Host E) (b : Bool) : ℂ := if b then H.rt0 else -H.rt0

structure LatData {D : Datum H} {g : ℕ} {ty : Fin g → (E →+* ℂ)} {Pe : D.La →+ (Fin g → ℂ)} (hP : IsPeriod D ty Pe)
    (Λ : ℝ) where
  A : Bool → Datum H
  sigP : (A true).p = 1 ∧ (A true).q = 0
  sigM : (A false).p = 0 ∧ (A false).q = 1
  ψ : ∀ j : Fin D.p ⊕ Fin D.q, (A j.isLeft).La →ₗ[𝓞 E] D.La
  hh : Fin D.p ⊕ Fin D.q → 𝓞 E
  pure : ∀ j a, ψ j a ∈ PureType.lat hP (typeVal H j.isLeft)
  form : ∀ j a b, D.EF (ψ j a) (ψ j b) = (A j.isLeft).EF (hh j • a) b
  span : ∀ x : D.La, ∃ N : ℕ, 0 < N ∧ N • x ∈ ⨆ j, LinearMap.range (ψ j)
  one_le : 1 ≤ Λ
  bound : ∀ j (τ : E →+* ℂ), ‖τ (hh j : E)‖ ≤ Λ ^ 2

namespace LatData

end LatData

end GlobalTheory.IndefiniteRowSideFullHecke.LogarithmicDifferentialCharacter
end
