import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRangeOfSteps

noncomputable section

open scoped TensorProduct NNReal Matrix Topology
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.Doubling

namespace GlobalTheory.SWInt

open GlobalTheory.SWLit GlobalTheory.SWWeil

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) {n m : ℕ}
  {J₂ : Matrix (Fin (n + n)) (Fin (n + n)) E}

variable {σ}

section Sec

variable {JV : Matrix (Fin m) (Fin m) E} {κ : Type} (om : UA σ JV × UA σ J₂ →* Module.End ℂ ((κ → AF F) → ℂ))
  (K : Subgroup (UA σ J₂))

def secMap : ((κ → AF F) → ℂ) →ₗ[ℂ] (UA σ J₂ → ℂ) where
  toFun Φ g := om (1, g) Φ 0
  map_add' Φ Ψ := funext fun g => by simp
  map_smul' a Φ := funext fun g => by simp

omit [NumberField E] in

@[simp] theorem secMap_apply (Φ : (κ → AF F) → ℂ) (g : UA σ J₂) : secMap om Φ g = om (1, g) Φ 0 := rfl

variable [Fintype κ]

variable {om K}

end Sec

end GlobalTheory.SWInt

end
