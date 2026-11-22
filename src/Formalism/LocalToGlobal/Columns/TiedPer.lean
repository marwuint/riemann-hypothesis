import Formalism.LocalToGlobal.Columns.TiedValFi
import Formalism.LocalToGlobal.Columns.RecordInst

open NumberField IsDedekindDomain Module Matrix
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.UG Formalism.L2.Forms

namespace GSD.Ev

end GSD.Ev

namespace GSD

variable {K : Type} [Field K] [NumberField K] [StarRing K]

structure Dua (S S' : GSD K) where
  eG : S.G ≃ S'.G
  eD : S.D ≃ S'.D
  smul : ∀ (g : S.G) (d : S.D), eD (g • d) = eG g • eD d

  B : S.V →ₗ[K] S'.V →ₗ[K] K
  inv : ∀ (g : S.G) (x : S.V) (y : S'.V), B (S.ρ g x) (S'.ρ (eG g) y) = B x y
  repr : ∀ ℓ : S.V →ₗ[K] K, ∃ y : S'.V, ∀ x, B x y = ℓ x
  ext : ∀ y y' : S'.V, (∀ x, B x y = B x y') → y = y'

namespace Dua

variable {S S' : GSD K} (P : Dua S S') (σ : K →+* ℂ)

def semi (y : S'.V) : S.V →ₛₗ[σ] ℂ where
  toFun x := σ (P.B x y)
  map_add' x x' := by rw [map_add, LinearMap.add_apply, map_add]
  map_smul' a x := by rw [map_smul, LinearMap.smul_apply, smul_eq_mul, map_mul, smul_eq_mul]

theorem semi_apply (y : S'.V) (x : S.V) : P.semi σ y x = σ (P.B x y) := rfl

variable {σ} (E : S.Ev σ) {ι : Type} [Fintype ι]

def jOf (b : ι → S'.EqFun) (z : ι → ℂ) : S.Cl → E.Y → ℂ :=
  fun c => ∑ a, starRingEnd ℂ (z a) • E.sharp (P.semi σ ((b a : S'.D → S'.V) (P.eD (S.outSec.rep c))))

end Dua

end GSD

section Pair

variable {E K : Type} [Field E] [Field K] {ι : Type} [Fintype ι] {n : ℕ}

end Pair

section Xp

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) {SG' : Finset (HeightOneSpectrum (𝓞 X.E))}
  (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x)) (hM : (rowGSD W ΛM).Ok)

end Xp

end Formalism.L2.Col
