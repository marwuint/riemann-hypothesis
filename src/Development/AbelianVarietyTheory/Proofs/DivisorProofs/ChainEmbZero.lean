import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev

noncomputable section

namespace GlobalTheory.ThK.FlagCT

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def chainEmb {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1)))
    (k : ℕ) : Matrix (Fin d) (Fin (d₁ - 2 * k)) E :=
  Nat.rec (motive := fun k => Matrix (Fin d) (Fin (d₁ - 2 * k)) E) H'.ι (fun k M => M * (pl k).ι) k

def flagX {d d₁ : ℕ} (H' : Plane E d d₁) (pl : ∀ j : ℕ, Plane E (d₁ - 2 * j) (d₁ - 2 * (j + 1))) (r : ℕ) :
    Matrix (Fin d) (Fin r) E :=
  Matrix.of fun a k => if k.1 = 0 then H'.x a else (chainEmb H' pl (k.1 - 1) *ᵥ (pl (k.1 - 1)).x) a

end GlobalTheory.ThK.FlagCT

end
