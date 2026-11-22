import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.ThK.EvAt0

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def colEq {d d₁ : ℕ} (h : d = d₁ + 2) : Fin d ≃ Fin d₁ ⊕ Fin 2 := (finCongr h).trans finSumFinEquiv.symm

def idx {n d d₁ : ℕ} (h : d = d₁ + 2) : Fin n × Fin d ≃ (Fin n × Fin d₁) ⊕ (Fin n × Fin 2) :=
  (Equiv.prodCongr (Equiv.refl _) (colEq h)).trans (Equiv.prodSumDistrib _ _ _)

variable (σ : E →ₐ[F] E) {n d d₁ : ℕ} (h2 : Module.finrank F E = 2) (X : Spc F E n) (W : Spc F E d) {W₁ : Spc F E d₁}
  (h : d = d₁ + 2) (H' : Plane E d d₁) (M₁ : Model σ X W₁)

omit σ h2 X W H' M₁

end GlobalTheory.ThK.EvAt0
