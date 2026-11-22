import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

noncomputable section

namespace GlobalTheory.ThKCtFin

open scoped TensorProduct NNReal Matrix
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

variable (σ : E →ₐ[F] E) in

def leviElt {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (t : (AE F E)ˣ) : UA σ W.J := by
  classical
  exact if h : ∃ m : UA σ W.J, IsLevi (W₁ := W₁) H' t 1 m then h.choose else 1

variable (σ : E →ₐ[F] E) in

def ctLevi {d d₁ : ℕ} (W : Spc F E d) (W₁ : Spc F E d₁) (H' : Plane E d d₁) (μ : Measure (unip σ W H'))
    (𝓕 : Set (unip σ W H')) (f : UA σ W.J → ℂ) (h : UA σ W.J) (t : (AE F E)ˣ) : ℂ :=
  ∫ u in 𝓕, f (u.1 * (leviElt σ W W₁ H' t * h)) ∂μ

end GlobalTheory.ThKCtFin
