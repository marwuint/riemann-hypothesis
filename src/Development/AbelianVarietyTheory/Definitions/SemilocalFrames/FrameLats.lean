import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.InFrameStabilizer

noncomputable section

open NumberField Matrix GlobalTheory.SgAlg
open scoped nonZeroDivisors

namespace GlobalTheory.SgGlob

variable {E : Type} [Field E] [NumberField E]

def dInv (E : Type) [Field E] [NumberField E] (j : ℕ) : FractionalIdeal (𝓞 E)⁰ E :=
  ((differentIdeal ℤ (𝓞 E) : FractionalIdeal (𝓞 E)⁰ E)⁻¹) ^ j

def SelfDual (σ : E →+* E) {n : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  Λ.FG ∧ ∀ v, v ∈ Λ ↔ ∀ w ∈ Λ, form σ J v w ∈ (algebraMap (𝓞 E) E).range

def frameLat {n r : ℕ} (P : Matrix (Fin n) (Fin (r + 1)) E) : Submodule (𝓞 E) (Fin n → E) :=
  Submodule.span (𝓞 E) {v | ∃ (b : Fin (r + 1)) (a : E), a ∈ dInv E (r - (b : ℕ)) ∧ v = a • fun i => P i b}

def PrimIn {n : ℕ} (M Λ : Submodule (𝓞 E) (Fin n → E)) : Prop :=
  M ≤ Λ ∧ ∀ v ∈ Λ, v ∈ Submodule.span E (M : Set (Fin n → E)) → v ∈ M

def latMap {n : ℕ} (γ : Matrix (Fin n) (Fin n) E) (Λ : Submodule (𝓞 E) (Fin n → E)) :
    Submodule (𝓞 E) (Fin n → E) := Λ.map (γ.mulVecLin.restrictScalars (𝓞 E))

def IsoLz (σ : E →+* E) {m : ℕ} (Jb : Matrix (Fin m) (Fin m) E) (γ : Matrix (Fin m) (Fin m) E)
    (x y : Submodule (𝓞 E) (Fin m → E) × (Fin m → E)) : Prop :=
  IsUn σ Jb γ ∧ latMap γ x.1 = y.1 ∧ γ.mulVec x.2 = y.2

def FrameLats (σ : E →+* E) {n r : ℕ} (J : Matrix (Fin n) (Fin n) E)
    (P : Matrix (Fin n) (Fin (r + 1)) E) : Set (Submodule (𝓞 E) (Fin n → E)) :=
  {Λ | SelfDual σ J Λ ∧ PrimIn (frameLat P) Λ}

end GlobalTheory.SgGlob
