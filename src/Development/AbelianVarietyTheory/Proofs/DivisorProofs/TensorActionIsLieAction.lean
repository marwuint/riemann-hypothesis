import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RestrActApply

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg GlobalTheory.SteepMult

namespace GlobalTheory.SteepMult.TLie

variable {R S : ℕ}

variable {W : Type} [AddCommGroup W] [Module ℂ W]

lemma factorOp_apply (k : ℕ) (i : Fin k) (Z : Mat R S) (Ψ : (Fin k → NC R S) → W) (g : Fin k → NC R S) :
    factorOp k i Z Ψ g = ∑ x, adP Z (g i) x • Ψ (Function.update g i x) := rfl

def ptOp (k : ℕ) (A : Module.End ℂ W) : Module.End ℂ ((Fin k → NC R S) → W) :=
  LinearMap.pi (fun g => A ∘ₗ LinearMap.proj g)

lemma tAct_eq (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) (Z : Mat R S) :
    tAct k actW Z = ptOp k (actW Z) + ∑ i, factorOp k i Z := rfl

end GlobalTheory.SteepMult.TLie
