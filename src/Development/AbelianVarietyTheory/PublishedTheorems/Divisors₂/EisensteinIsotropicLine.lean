import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EventuallyAlgebraMapMemIntegers

noncomputable section

open NumberField MeasureTheory Matrix Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open Formalism.UG (cT bc)
open GlobalTheory.Doubling (absE)
open scoped TensorProduct NNReal

namespace GlobalTheory.EisLine

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  (σ : E →ₐ[F] E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E) {r : ℕ}

structure IsAdapted (X Y : Matrix (Fin n) (Fin r) E) (L : Submodule (𝓞 E) (Fin n → E))
    (a : GL (Fin n) (AF F ⊗[F] E)) : Prop where
  lat : Submodule.IsLattice E L
  dual : ∀ v, IsSelfDualAt σ J L v
  split : ∀ z ∈ L, ∀ i, ((cT (σ : E →+* E) Y * J) *ᵥ z) i • Xᵀ i ∈ L ∧ ((cT (σ : E →+* E) X * J) *ᵥ z) i • Yᵀ i ∈ L
  maj : IsMajorantFrame σ J a
  cartan : ∀ w : InfinitePlace F, ∃ c : Fin r → w.Completion ⊗[F] E,
    cT (sigR _ σ) (bc (compInf F E w) a⁻¹).1 * (bc (compInf F E w) a⁻¹).1 * X.map (inclR (F := F) w.Completion) =
      (JR w.Completion J * Y.map (inclR (F := F) w.Completion) : Matrix (Fin n) (Fin r) (w.Completion ⊗[F] E)) * diagonal c

def IsModerateForm (μ : (GAd σ J → ℂ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ N : ℕ, ∃ (S : List (List (ℝ → GAd σ J))) (C : ℝ), (∀ l ∈ S, ∀ γ ∈ l, IsRealLine σ J γ) ∧
    ∀ f, IsSmoothModerate σ J f →
      (∀ l : List (ℝ → GAd σ J), (∀ γ ∈ l, IsRealLine σ J γ) →
        ∃ B : ℝ, ∀ g, ‖l.foldr lineDer f g‖ ≤ B * (height σ J g : ℝ) ^ N) →
      (∀ l ∈ S, ∀ g, ‖l.foldr lineDer f g‖ ≤ (height σ J g : ℝ) ^ N) → ‖μ f‖ ≤ C

end GlobalTheory.EisLine

namespace GlobalTheory.Published

open GlobalTheory.EisLine in

def EisensteinIsotropicLine : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    Algebra.Unramified (𝓞 F) (𝓞 E) →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin (r + 1)) E), IsWittFrame σ J X Y →
      ∀ (x y : Matrix (Fin n) (Fin 1) E), x = X.submatrix id (fun _ => 0) → y = Y.submatrix id (fun _ => 0) →
      ∀ (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (AF F ⊗[F] E)), IsAdapted σ J X Y L a →
      ∀ h : GAd σ J → ℝ,
        (∀ g, ∃ p, ∃ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x ∧
          ∃ k ∈ levelAll σ J L a, g = p * k) →
        (∀ p, ∀ l : (AF F ⊗[F] E)ˣ, (matHom _ σ J p).1 * adMat F x = l.1 • adMat F x →
          ∀ k ∈ levelAll σ J L a, h (p * k) = absE F E l) →
      ∃ (Eis : ℂ → GAd σ J → ℂ) (c : ℂ → ℂ),
        (∀ T : Set (ratPts σ J), (∀ γ : ratPts σ J, ∃! t, t ∈ T ∧ ∃ l : (AF F ⊗[F] E)ˣ,
            (matHom _ σ J (γ * t⁻¹ : ratPts σ J).1).1 * adMat F x = l.1 • adMat F x) →
          ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
            HasSum (fun t : T => (h (t.1.1 * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) (Eis s g)) ∧
        (∀ w ∈ ratPts σ J, (matHom _ σ J w).1 * adMat F y = adMat F x →
          ∀ (μ : Measure (unipRad σ J x)) (𝓕 : Set (unipRad σ J x)), μ.IsHaarMeasure →
            IsFundamentalDomain ((ratPts σ J).subgroupOf (unipRad σ J x)) 𝓕 μ → μ 𝓕 = 1 →
            ∀ s : ℂ, ((n : ℝ) - 1) / 2 < s.re → ∀ g,
              Integrable (fun u : unipRad σ J x => (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2)) μ ∧
              ∫ u : unipRad σ J x, (h (w * u * g) : ℂ) ^ (s + ((n : ℂ) - 1) / 2) ∂μ =
                c s * (h g : ℂ) ^ (-s + ((n : ℂ) - 1) / 2)) ∧
        MeromorphicOn c Set.univ ∧
        (∀ s₀ : ℂ, ∃ (k : ℕ) (U : Set ℂ) (H : ℂ → GAd σ J → ℂ), U ∈ 𝓝 s₀ ∧
          (∀ s ∈ U, s ≠ s₀ → ∀ g, H s g = (s - s₀) ^ k * Eis s g) ∧ (∀ s ∈ U, IsSmoothModerate σ J (H s)) ∧
          ∀ μ, IsModerateForm σ J μ → DifferentiableOn ℂ (fun s => μ (H s)) U) ∧
        ∀ s₀ : ℂ, ∀ᶠ s in 𝓝[≠] s₀, c s * c (-s) = 1 ∧ ∀ g, Eis s g = c s * Eis (-s) g

end GlobalTheory.Published

end
