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

lemma adCoeff_add (Z Z' : Mat R S) (y x : NC R S) : adP (Z + Z') y x = adP Z y x + adP Z' y x := by
  simp only [adP, Matrix.add_apply]; ring

lemma adCoeff_smul (c : ℂ) (Z : Mat R S) (y x : NC R S) : adP (c • Z) y x = c * adP Z y x := by
  simp only [adP, Matrix.smul_apply, smul_eq_mul]; ring

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def factorOp (k : ℕ) (i : Fin k) (Z : Mat R S) : Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Ψ g := ∑ x, adP Z (g i) x • Ψ (Function.update g i x)
  map_add' Ψ Φ := by ext g; simp [Finset.sum_add_distrib]
  map_smul' c Ψ := by ext g; simp [Finset.smul_sum, smul_comm c]

def tAct (k : ℕ) (actW : Mat R S →ₗ[ℂ] Module.End ℂ W) : Mat R S →ₗ[ℂ] Module.End ℂ ((Fin k → NC R S) → W) where
  toFun Z := LinearMap.pi (fun g => actW Z ∘ₗ LinearMap.proj g) + ∑ i, factorOp k i Z
  map_add' Z Z' := by
    ext Ψ g
    simp [factorOp, adCoeff_add, add_smul, Finset.sum_add_distrib]
    abel
  map_smul' c Z := by
    ext Ψ g
    simp [factorOp, adCoeff_smul, mul_smul, Finset.smul_sum]

def formT (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) :
    ((Fin k → NC R S) → W) →ₗ⋆[ℂ] ((Fin k → NC R S) → W) →ₗ[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) (fun Ψ Φ => ∑ g, B (Ψ g) (Φ g))
    (fun Ψ Ψ' Φ => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])
    (fun Ψ Φ Φ' => by simp [Finset.sum_add_distrib])
    (fun c Ψ Φ => by simp [Finset.mul_sum])

lemma formT_apply (k : ℕ) (B : W →ₗ⋆[ℂ] W →ₗ[ℂ] ℂ) (Ψ Φ : (Fin k → NC R S) → W) :
    formT k B Ψ Φ = ∑ g, B (Ψ g) (Φ g) := rfl

def kpart (Z : Mat R S) : Mat R S := Matrix.of fun a b => if sameBlock a b then Z a b else 0

lemma isKC_kpart (Z : Mat R S) : IsKC (kpart Z) := fun a b h => by simp [kpart, h]

variable {V : Type} [AddCommGroup V] [Module ℂ V]

def restrAct (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) :
    Mat R S →ₗ[ℂ] Module.End ℂ N where
  toFun Z := (act (kpart Z)).restrict fun x hx => hN _ (isKC_kpart Z) x hx
  map_add' Z Z' := by
    ext x
    have : kpart (Z + Z') = kpart Z + kpart Z' := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]
  map_smul' c Z := by
    ext x
    have : kpart (c • Z) = c • kpart Z := by ext a b; by_cases h : sameBlock a b <;> simp [kpart, h]
    simp [this]

lemma restrAct_apply (act : Mat R S →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V) (hN : KStable act N) (Z : Mat R S)
    (x : N) : (restrAct act N hN Z x : V) = act (kpart Z) x := rfl

end GlobalTheory.SteepMult

end
