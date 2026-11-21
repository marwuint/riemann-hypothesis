import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ScalarOnPartsFull
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfInnerSmooth

noncomputable section

open Formalism.MainNotions.S Formalism.L2.Theta Formalism.QuantumDeterminants GlobalTheory.SmVec Matrix

namespace GlobalTheory.RealBessel

variable {n m r : ℕ}

structure IsFrame (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Prop where
  herm : Jᴴ = J
  unit : IsUnit J
  unit₀ : IsUnit J₀
  codim : m + 2 * r + 1 = n
  gram : Fᴴ * J * F = J₀
  e_indep : LinearIndependent ℂ eᵀ
  e_iso : eᴴ * J * e = 0
  e_perp : Fᴴ * J * e = 0
  z_perpF : (Fᴴ * J) *ᵥ z = 0
  z_perpE : (eᴴ * J) *ᵥ z = 0
  z_ne : Formalism.QuantumDeterminants.herm J z z ≠ 0

def unipRad (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) : Set (Matrix (Fin n) (Fin n) ℂ) :=
  {u | u ∈ UH J ∧
    (∀ i : Fin r, ∃ a : Fin r → ℂ, (∀ j, i ≤ j → a j = 0) ∧ (u - 1) *ᵥ (fun k => e k i) = e *ᵥ a) ∧
    ∀ x : Fin n → ℂ, (eᴴ * J) *ᵥ x = 0 → ∃ a : Fin r → ℂ, (u - 1) *ᵥ x = e *ᵥ a}

def flagVec (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) : Fin (r + 1) → Fin n → ℂ :=
  Fin.snoc (α := fun _ => Fin n → ℂ) (fun i k => e k i) z

def IsCharWith (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ) (c : Fin r → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∀ u ∈ unipRad J e, ∀ a : Fin r → Fin r → ℂ, (∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j) →
    χ u = Complex.exp (Complex.I * ((∑ j, c j * a j j).re : ℂ))

def IsGeneric (J : Matrix (Fin n) (Fin n) ℂ) (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ)
    (χ : Matrix (Fin n) (Fin n) ℂ → ℂ) : Prop :=
  ∃ c : Fin r → ℂ, (∀ j, c j ≠ 0) ∧ IsCharWith J e z c χ

def IsEmb (J : Matrix (Fin n) (Fin n) ℂ) (F : Matrix (Fin n) (Fin m) ℂ) (g : Matrix (Fin n) (Fin n) ℂ)
    (h : Matrix (Fin m) (Fin m) ℂ) : Prop :=
  g * F = F * h ∧ ∀ x : Fin n → ℂ, (Fᴴ * J) *ᵥ x = 0 → g *ᵥ x = x

section Forms

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {W : Type} [AddCommGroup W] [Module ℂ W]

def IsContIrred (G : Set (Matrix (Fin m) (Fin m) ℂ)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W) : Prop :=
  IsRepOn G π₀ ∧ (∀ (w : W) (l : Module.Dual ℂ W), ContinuousOn (fun h => l (π₀ h w)) G) ∧
    ∀ U : Submodule ℂ W, (∀ h ∈ G, ∀ w ∈ U, π₀ h w ∈ U) → U = ⊥ ∨ U = ⊤

structure IsBesselForm (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) (β : W →ₗ[ℂ] V →ₗ[ℂ] ℂ) : Prop where
  cont : ∀ w : W, ∃ l : H →ₗ[ℂ] ℂ, Sobolev₂ (lieG J) σ l ∧ ∀ x : V, l x = β w x
  inv : ∀ h ∈ UH J₀, ∀ g ∈ UH J, IsEmb J F g h → ∀ (w : W) (x y : V), (y : H) = σ g x → β (π₀ h w) y = β w x
  equiv : ∀ u ∈ unipRad J e, ∀ (w : W) (x y : V), (y : H) = σ u x → β w y = χ u * β w x

def besselForms (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (χ : Matrix (Fin n) (Fin n) ℂ → ℂ)
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W)
    (V : Submodule ℂ H) : Submodule ℂ (W →ₗ[ℂ] V →ₗ[ℂ] ℂ) where
  carrier := {β | IsBesselForm J J₀ F e χ σ π₀ V β}
  zero_mem' := ⟨fun _ => ⟨0, ⟨[], 0, by simp, by simp⟩, fun _ => rfl⟩, fun _ _ _ _ _ _ _ _ _ => rfl,
    fun _ _ _ _ _ _ => by simp⟩
  add_mem' := fun {β β'} hβ hβ' =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      obtain ⟨l', h1', h2'⟩ := hβ'.cont w
      exact ⟨l + l', GlobalTheory.MultMem.sobCont_add h1 h1', fun x => by simp [h2, h2']⟩,
    fun h hh g hg hE w x y hy => by
      simp only [LinearMap.add_apply, hβ.inv h hh g hg hE w x y hy, hβ'.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.add_apply, hβ.equiv u hu w x y hy, hβ'.equiv u hu w x y hy, mul_add]⟩
  smul_mem' := fun c β hβ =>
    ⟨fun w => by
      obtain ⟨l, h1, h2⟩ := hβ.cont w
      exact ⟨c • l, GlobalTheory.MultMem.sobCont_smul c h1, fun x => by simp [h2]⟩,
    fun h hh g hg hE w x y hy => by simp only [LinearMap.smul_apply, hβ.inv h hh g hg hE w x y hy],
    fun u hu w x y hy => by
      simp only [LinearMap.smul_apply, hβ.equiv u hu w x y hy, smul_eq_mul, mul_left_comm]⟩

end Forms

variable {J : Matrix (Fin n) (Fin n) ℂ} {J₀ : Matrix (Fin m) (Fin m) ℂ} {F : Matrix (Fin n) (Fin m) ℂ}
  {e : Matrix (Fin n) (Fin r) ℂ} {z : Fin n → ℂ}

theorem IsFrame.exists_coords (hf : IsFrame J J₀ F e z) {u : Matrix (Fin n) (Fin n) ℂ} (hu : u ∈ unipRad J e) :
    ∃ a : Fin r → Fin r → ℂ, ∀ j : Fin r, (u - 1) *ᵥ flagVec e z j.succ = e *ᵥ a j := by
  have : ∀ i : Fin (r + 1), ∃ a, (u - 1) *ᵥ flagVec e z i = e *ᵥ a := fun i => by
    refine Fin.lastCases ?_ (fun j => ?_) i
    · simpa [flagVec] using hu.2.2 z hf.z_perpE
    · obtain ⟨a, -, ha⟩ := hu.2.1 j
      exact ⟨a, by simpa [flagVec] using ha⟩
  exact ⟨fun j => (this j.succ).choose, fun j => (this j.succ).choose_spec⟩

end GlobalTheory.RealBessel

namespace GlobalTheory.Published

open GlobalTheory.RealBessel

def BesselUniquenessReal : Prop :=
  ∀ (n m r : ℕ) (J : Matrix (Fin n) (Fin n) ℂ) (J₀ : Matrix (Fin m) (Fin m) ℂ) (F : Matrix (Fin n) (Fin m) ℂ)
    (e : Matrix (Fin n) (Fin r) ℂ) (z : Fin n → ℂ), IsFrame J J₀ F e z →
    ∀ χ : Matrix (Fin n) (Fin n) ℂ → ℂ, IsGeneric J e z χ →
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
      (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsURepOn (UH J) σ → IsIrredOn (UH J) σ →
    ∀ (W : Type) [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
      (π₀ : Matrix (Fin m) (Fin m) ℂ → Module.End ℂ W), IsContIrred (UH J₀) π₀ →
      Module.rank ℂ (besselForms J J₀ F e χ σ π₀ (smSub J σ)) ≤ 1

end GlobalTheory.Published

end
