import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt

noncomputable section

namespace GlobalTheory.ConeSoB

open MeasureTheory Filter
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d n₁ d₁ : ℕ} {X : Spc F E n} {W : Spc F E d}

variable (B : Base F E) (M : Model σ X W) (om : Rep σ X W) (e : Fn F n d →ₗ[ℂ] Fn F n₁ d₁) (K : Subgroup (UA σ X.J))
  (μK : Measure K) (μ : Measure (AE F E)ˣ) (u : (AE F E)ˣ → Matrix (Fin n) (Fin d) (AE F E)) (ν : Chr F E) (z : ℕ)

def coneInt (Φ : Fn F n d) (k : UA σ X.J) (l : (AE F E)ˣ) (y : Fin n₁ × Fin d₁ → AF F) : ℂ :=
  e (M.co.rho B.ψ (u l) (om (k, 1) Φ)) y * (ν l : ℂ) * ((absE F E l : ℝ) : ℂ) ^ z

theorem cone_apply (Φ : Fn F n d) (y : Fin n₁ × Fin d₁ → AF F) :
    cone B M om e K μK μ u ν z Φ y = ∫ k, ∫ l, coneInt B M om e u ν z Φ k.1 l y ∂μ ∂μK := rfl

variable {B M om e K μK μ u ν z}

end GlobalTheory.ConeSoB
