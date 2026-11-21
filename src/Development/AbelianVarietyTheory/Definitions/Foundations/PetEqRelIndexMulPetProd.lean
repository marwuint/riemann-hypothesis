import Mathlib

noncomputable section

open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm

namespace GlobalTheory.Hk

def lev (N l : ℕ) : Subgroup SL(2, ℤ) := Gamma1 N ⊓ Gamma0 l

def uOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ :=
  (q : ℂ)⁻¹ * ∑ j ∈ Finset.range q, f (ofComplex (((τ : ℂ) + j) / q))

def vOp (q : ℕ) (f : ℍ → ℂ) (τ : ℍ) : ℂ := f (ofComplex ((q : ℂ) * τ))

def IsDia (N l : ℕ) (d : ℤ) (σ : SL(2, ℤ)) : Prop :=
  ((σ 1 0 : ℤ) : ZMod (N * l)) = 0 ∧ ((σ 1 1 : ℤ) : ZMod N) = d

def dia (k : ℤ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ := f ∣[k] σ

def heckeT (k : ℤ) (q : ℕ) (σ : SL(2, ℤ)) (f : ℍ → ℂ) : ℍ → ℂ :=
  uOp q f + ((q : ℂ) ^ (k - 1)) • vOp q (f ∣[k] σ)

def coef (f : ℍ → ℂ) (n : ℕ) : ℂ := (qExpansion 1 f).coeff n

def pet (Γ : Subgroup SL(2, ℤ)) (k : ℤ) (f g : ℍ → ℂ) : ℂ :=
  ∑ᶠ γ : SL(2, ℤ) ⧸ Γ, ∫ z in ModularGroup.fd, petersson k f g (γ.out⁻¹ • z)

def pmGrp (Γ : Subgroup SL(2, ℤ)) : Subgroup SL(2, ℤ) where
  carrier := {γ | γ ∈ Γ ∨ -γ ∈ Γ}
  one_mem' := Or.inl Γ.one_mem
  mul_mem' := by
    rintro a b (ha | ha) (hb | hb)
    · exact Or.inl (Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inr (by simpa using Γ.mul_mem ha hb)
    · exact Or.inl (by simpa using Γ.mul_mem ha hb)
  inv_mem' := by
    rintro a (ha | ha)
    · exact Or.inl (Γ.inv_mem ha)
    · refine Or.inr ?_
      have h : -a⁻¹ = (-a)⁻¹ := by
        rw [eq_inv_iff_mul_eq_one]; simp
      rw [h]; exact Γ.inv_mem ha

theorem le_pmGrp (Γ : Subgroup SL(2, ℤ)) : Γ ≤ pmGrp Γ := fun _ h => Or.inl h

instance pmGrp_finiteIndex (Γ : Subgroup SL(2, ℤ)) [Γ.FiniteIndex] : (pmGrp Γ).FiniteIndex :=
  Subgroup.finiteIndex_of_le (le_pmGrp Γ)

end GlobalTheory.Hk
