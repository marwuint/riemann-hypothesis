import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.IndLine

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
variable {n d : ℕ} {Y : Spc F E n} {W : Spc F E d}

def fockDeg (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w)
    (k : ℕ) : Submodule ℂ (SInf F (Fin n × Fin d)) :=
  Nat.rec (motive := fun _ => Submodule ℂ (SInf F (Fin n × Fin d))) (Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀})
    (fun _ N => N ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ N, ActsD (evI F) (M.heisLine ψ u) f f₁}) k

theorem fockDeg_zero (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) :
    fockDeg M ψ τ 0 = Submodule.span ℂ {f₀ | M.IsGauss ψ τ f₀} := rfl

theorem fockDeg_succ (M : Model σ Y W) (ψ : AddChar (AF F) ℂ) (τ : ∀ w : InfinitePlace F, EmbOver E w) (k : ℕ) :
    fockDeg M ψ τ (k + 1) = fockDeg M ψ τ k ⊔ Submodule.span ℂ {f₁ | ∃ u, At (evI F) u ∧ ∃ f ∈ fockDeg M ψ τ k,
      ActsD (evI F) (M.heisLine ψ u) f f₁} := rfl

end GlobalTheory.IndLine
