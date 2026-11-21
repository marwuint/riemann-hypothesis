import Mathlib
import Formalism.MirabolicMackeyTheory.StatementL
import Formalism.MirabolicMackeyTheory.StatementT

open Module NumberField IsDedekindDomain

noncomputable section

namespace Formalism.EigenvalueLevelCeiling

open Formalism.DivisionValues

def OnLocalJ : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th ThK Th0 ThJ X₃ X₄ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ → IsLatIn (eig ρ U ψ ⊓ V₀) X₄ → X₃ ≤ X₄ →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) = X₄ →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

def ThetaIdentity : Prop :=
  ∀ (R X Y : Type) [CommRing R] [AddCommGroup X] [Module R X] [AddCommGroup Y] [Module R Y]
    (θ : X →ₗ[R] Y) (eX pr : X →ₗ[R] X) (e : Y →ₗ[R] Y),
    θ ∘ₗ eX = e ∘ₗ θ → (∀ x ∈ LinearMap.range eX, x - pr x ∈ LinearMap.ker θ) →
    ∀ Mt : Submodule R X, ((Mt.map eX).map pr).map θ = (Mt.map θ).map e

def EnlargeInitialLattice : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (M Th1 Th : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th1 → IsLatIn ⊤ Th → Th1 ≤ Th → Th ≤ M →
    ∀ (E r : ℝ),
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th1) : ℝ) ≤ E * (finrank K W : ℝ) + r) →
    ∀ W : Submodule K Z, (lix w (cut W M) (cut W Th) : ℝ) ≤ E * (finrank K W : ℝ) + r

def TwChain : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (W : Submodule K Z) (e : Z →ₗ[K] Z) (A Th0 ThJ X₃ : Submodule (𝓞 K) Z),
    IsLatIn W A → IsLatIn W (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn W (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    ∀ ε : ℝ, (lix w A X₃ : ℝ) ≤ (lix w A (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
      (lix w A X₃ : ℝ) ≤ (lix w A (Th0.map (e.restrictScalars (𝓞 K))) : ℝ) + ε

def LocalConditionsWeighted : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [StarRing K] (Z : Type) [AddCommGroup Z] [Module K Z]
    [Module (𝓞 K) Z] [IsScalarTower (𝓞 K) K Z] [FiniteDimensional K Z]
    (w : HeightOneSpectrum (𝓞 K)) (P : Type) [Group P] [Finite P] (ρ : Representation K P Z)
    (U : Subgroup P) (ψ : P → 𝓞 K), IsMackey U ψ →
    ∀ (V₀ : Submodule K Z) (e : Z →ₗ[K] Z), e ∘ₗ e = e → LinearMap.range e = V₀ →
    ∀ (M Th1 Th ThK Th0 ThJ X₃ : Submodule (𝓞 K) Z),
    IsLatIn ⊤ M → IsLatIn ⊤ Th1 → IsLatIn ⊤ Th → IsLatIn ⊤ ThK → Th1 ≤ Th → Th ≤ M → Th0.FG →
    Th0 ≤ (eig ρ U ψ).restrictScalars (𝓞 K) →
    (∀ g : P, M.map ((ρ g).restrictScalars (𝓞 K)) ≤ M) →
    (∀ g : P, Th.map ((ρ g).restrictScalars (𝓞 K)) ≤ Th) →
    ∀ (σ : K), σ ≠ 0 → Th ≤ sc σ ThK →
    sc ((Nat.card U : ℕ) : K) (cut (eig ρ U ψ) ThK) ≤ Th0 →
    ∀ (a : K) (E : ℕ) (r : ℝ), a ≠ 0 → vw w a = (E : ℤ) →
    (∀ W : Submodule K Z, (lix w (cut W M) (cut W Th1) : ℝ) ≤ (E : ℝ) * (finrank K W : ℝ) + r) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (Th0.map (e.restrictScalars (𝓞 K))) →
    IsLatIn (eig ρ U ψ ⊓ V₀) (ThJ.map (e.restrictScalars (𝓞 K))) → Th0 ≤ ThJ →
    IsLatIn (eig ρ U ψ ⊓ V₀) X₃ →
    ∀ (X : Type) [AddCommGroup X] [Module K X] [Module (𝓞 K) X] [IsScalarTower (𝓞 K) K X]
      (θ' : X →ₗ[K] Z) (eX pr : X →ₗ[K] X) (Mt : Submodule (𝓞 K) X),
    θ' ∘ₗ eX = e ∘ₗ θ' → (∀ x ∈ LinearMap.range eX, x - pr x ∈ LinearMap.ker θ') →
    IsLatIn (eig ρ U ψ ⊓ V₀) ((Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K))) →
    X₃ ≤ (Mt.map (θ'.restrictScalars (𝓞 K))).map (e.restrictScalars (𝓞 K)) →
    ∀ (ε : ℝ),
    (lix w (cut (eig ρ U ψ ⊓ V₀) M) X₃ : ℝ) ≤
      (lix w (cut (eig ρ U ψ ⊓ V₀) M) (ThJ.map (e.restrictScalars (𝓞 K))) : ℝ) + ε →
    ∀ (d : ℕ) (φ : (Fin d → K) →ₗ[K] Z), Function.Injective φ →
    LinearMap.range φ = eig ρ U ψ ⊓ V₀ →
    ∀ (Mj Tj : Submodule (𝓞 K) (Fin d → K)),
    Mj.map (φ.restrictScalars (𝓞 K)) = cut (eig ρ U ψ ⊓ V₀) M →
    Tj.map (φ.restrictScalars (𝓞 K)) =
      ((Mt.map (eX.restrictScalars (𝓞 K))).map (pr.restrictScalars (𝓞 K))).map (θ'.restrictScalars (𝓞 K)) →
      (idx w Mj Tj : ℝ) ≤
        ((E : ℝ) - (vw w σ : ℝ) + (vw w ((Nat.card U : ℕ) : K) : ℝ)) * (d : ℝ) +
          (r + (finrank K Z : ℝ) * (vw w ((Nat.card U : ℕ) : K) : ℝ)) / (U.index : ℝ) + ε

end Formalism.EigenvalueLevelCeiling
