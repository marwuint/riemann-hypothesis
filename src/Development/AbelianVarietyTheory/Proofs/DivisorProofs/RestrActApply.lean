import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructure

noncomputable section

open Formalism.BasicNotions.TH GlobalTheory.FockAlg

namespace GlobalTheory.SteepMult

variable {R S : ℕ}

abbrev NC (R S : ℕ) : Type := {x : Ix R S × Ix R S // ¬ sameBlock x.1 x.2}

def adP (Z : Mat R S) (y x : NC R S) : ℂ :=
  Z y.1.1 x.1.1 * (if y.1.2 = x.1.2 then 1 else 0) - (if y.1.1 = x.1.1 then 1 else 0) * Z x.1.2 y.1.2

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def factorOp (k : ℕ) (i : Fin k) (Z : Mat R S) : Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Ψ g := ∑ x, adP Z (g i) x • Ψ (Function.update g i x)
  map_add' Ψ Φ := by ext g; simp [Finset.sum_add_distrib]
  map_smul' c Ψ := by ext g; simp [Finset.smul_sum, smul_comm c]

def formT (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) :
    ((Fin k → NC R S) → W) →ₗ⋆[ℂ] ((Fin k → NC R S) → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun Ψ Φ => ∑ g, B (Ψ g) (Φ g))
    (fun Ψ Ψ' Φ => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])
    (fun Ψ Φ Φ' => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])

def kpart (Z : Mat R S) : Mat R S := Matrix.of fun a b => if sameBlock a b then Z a b else 0

variable {V : Type} [AddCommGroup V] [Module ℂ V]

end GlobalTheory.SteepMult

end
