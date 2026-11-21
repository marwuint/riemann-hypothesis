import Mathlib
import Formalism.QuotientMetricDivisors.RatHermLcvTwist

open Module NumberField IsDedekindDomain
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.DivisionValues

def extSpan {K Ω : Type} [Field K] [Field Ω] {n : ℕ} (j : K →+* Ω) (Z : Submodule K (Fin n → K)) :
    Submodule Ω (Fin n → Ω) :=
  Submodule.span Ω ((fun z i => j (z i)) '' (Z : Set (Fin n → K)))

def IsAdjStable {K : Type} [Field K] [NumberField K] [StarRing K] {n : ℕ}
    (H : Matrix (Fin n) (Fin n) K) (𝒯 : Set (Matrix (Fin n) (Fin n) K)) : Prop :=
  ∀ T ∈ 𝒯, ∃ T' ∈ 𝒯, ∀ x y : Fin n → K, hform H (T.mulVec x) y = hform H x (T'.mulVec y)

def IsCommStable {K : Type} [Field K] {n : ℕ} (𝒯 : Set (Matrix (Fin n) (Fin n) K))
    (Z : Submodule K (Fin n → K)) : Prop :=
  ∀ B : Matrix (Fin n) (Fin n) K, (∀ T ∈ 𝒯, B * T = T * B) → ∀ z ∈ Z, B.mulVec z ∈ Z

def CommTwist : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (K0 : Subfield K), IsCMSub K0 →
    ∀ v0 : InfinitePlace K, IsConjAt v0 →
    ∀ (n : ℕ) (H : Matrix (Fin n) (Fin n) K), (∀ i j, H i j ∈ K0) →
    (∀ v : InfinitePlace K, (H.map v.embedding).PosDef) →
    ∀ 𝒯 : Set (Matrix (Fin n) (Fin n) K), (∀ T ∈ 𝒯, ∀ i j, T i j ∈ K0) →
    (∀ T ∈ 𝒯, ∀ T' ∈ 𝒯, T * T' = T' * T) → IsAdjStable H 𝒯 →
    ∀ Z : Submodule K (Fin n → K), IsCommStable 𝒯 Z →
    ∀ σ : K →+* ℂ, embSpan σ Z = embSpan (twist σ) Z

end Formalism.DivisionValues
