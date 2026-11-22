import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct NNReal Matrix

noncomputable section

namespace GlobalTheory.ThetaDecay

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def dH (ψ : AddChar (AF F) ℂ) (w : (κ → AF F) × (κ → AF F)) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  fun x => deriv (fun t : ℝ => schr ψ (realAd F t • w) Φ x) 0

def wordH (ψ : AddChar (AF F) ℂ) (l : List ((κ → AF F) × (κ → AF F))) (Φ : (κ → AF F) → ℂ) : (κ → AF F) → ℂ :=
  l.foldr (dH ψ) Φ

@[simp] theorem wordH_nil (ψ : AddChar (AF F) ℂ) (Φ : (κ → AF F) → ℂ) : wordH ψ [] Φ = Φ := rfl

end GlobalTheory.ThetaDecay

end
