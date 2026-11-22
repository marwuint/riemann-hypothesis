import Mathlib
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.ExistsEventuallyNormRiemannThetaTermLe

open Matrix MeasureTheory
open scoped Real ContDiff

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe

abbrev Fl (g : ℕ) : Type := Fin g ⊕ Fin g → ℝ

def riem {g : ℕ} (x y : Fl g) : ℝ :=
  ∑ i, (x (Sum.inr i) * y (Sum.inl i) - x (Sum.inl i) * y (Sum.inr i))

def symp (g : ℕ) : Fl g [⋀^Fin 2]→L[ℝ] ℝ where
  toFun v := riem (v 0) (v 1)
  map_update_add' := by
    intro inst v i x y
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, add_mul, mul_add, Finset.sum_add_distrib] <;> ring
  map_update_smul' := by
    intro inst v i c x
    obtain rfl : inst = instDecidableEqFin 2 := Subsingleton.elim _ _
    fin_cases i <;> simp [riem, ← Finset.sum_sub_distrib, Finset.mul_sum] <;>
      exact Finset.sum_congr rfl fun _ _ => by ring
  cont := by
    unfold riem
    fun_prop
  map_eq_zero_of_eq' := by
    intro v i j h hij
    have h01 : v 0 = v 1 := by
      fin_cases i <;> fin_cases j <;> simp_all
    simp only [riem, h01]
    exact Finset.sum_eq_zero fun _ _ => by ring

def stdLat (g : ℕ) : Submodule ℤ (Fl g) :=
  Submodule.span ℤ (Set.range (Pi.basisFun ℝ (Fin g ⊕ Fin g)))

def IsLat {g : ℕ} (M : Submodule ℤ (Fl g)) : Prop :=
  ∃ _ : DiscreteTopology M, IsZLattice ℝ M

def herm {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (v w : Fin g → ℂ) : ℂ :=
  (v ᵥ* ((τ.map Complex.im)⁻¹).map (fun t : ℝ => (t : ℂ))) ⬝ᵥ star w

def per {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (x : Fl g) : Fin g → ℂ :=
  (fun i => (x (Sum.inl i) : ℂ)) ᵥ* τ + fun i => (x (Sum.inr i) : ℂ)

def flatOf {g : ℕ} (τ : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) : Fl g :=
  Sum.elim ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹)
    ((fun i => (z i).re) - ((fun i => (z i).im) ᵥ* (τ.map Complex.im)⁻¹) ᵥ* τ.map Complex.re)

abbrev Sp (g : ℕ) : Type := Matrix.symplecticGroup (Fin g) ℝ

def Sp.mat {g : ℕ} (γ : Sp g) : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) ℝ := γ.1

def den {g : ℕ} (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  γ.mat.toBlocks₂₁.map (fun t : ℝ => (t : ℂ)) * τ + γ.mat.toBlocks₂₂.map (fun t : ℝ => (t : ℂ))

def moeb {g : ℕ} (γ : Sp g) (τ : Matrix (Fin g) (Fin g) ℂ) : Matrix (Fin g) (Fin g) ℂ :=
  (γ.mat.toBlocks₁₁.map (fun t : ℝ => (t : ℂ)) * τ + γ.mat.toBlocks₁₂.map (fun t : ℝ => (t : ℂ))) *
    (den γ τ)⁻¹

section Family

abbrev Pt (E : Type) (g : ℕ) : Type := E × (Fin g → ℂ)

variable {E E' : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup E'] [NormedSpace ℂ E'] {g : ℕ}

abbrev Form2 (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℕ) : Type :=
  Pt E g [⋀^Fin 2]→L[ℝ] ℝ

def IsPeriodMap (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) : Prop :=
  IsOpen B ∧ (∀ i j, DifferentiableOn ℂ (fun b => τ b i j) B) ∧ ∀ b ∈ B, IsSiegel (τ b)

def cov (B : Set E) (g : ℕ) : Set (Pt E g) := B ×ˢ Set.univ

def flat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Fl g := flatOf (τ P.1) P.2

def dflat (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Pt E g →L[ℝ] Fl g :=
  fderiv ℝ (flat τ) P

def om0 (τ : E → Matrix (Fin g) (Fin g) ℂ) (P : Pt E g) : Form2 E g :=
  (symp g).compContinuousLinearMap (dflat τ P)

def pull (f : Pt E g → Pt E' g) (α : Pt E' g → Form2 E' g) (P : Pt E g) : Form2 E g :=
  (α (f P)).compContinuousLinearMap (fderiv ℝ f P)

def transl (τ : E → Matrix (Fin g) (Fin g) ℂ) (x : Fl g) (P : Pt E g) : Pt E g :=
  (P.1, P.2 + per (τ P.1) x)

def ddc (u : Pt E g → ℝ) (P v w : Pt E g) : ℝ :=
  (1 / (4 * π)) * (fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • v)) P w -
    fderiv ℝ (fun Q => fderiv ℝ u Q (Complex.I • w)) P v)

def IsFactor (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  (∀ l ∈ M, DifferentiableOn ℂ (j l) (cov B g) ∧ ∀ P ∈ cov B g, j l P ≠ 0) ∧
  ∀ l ∈ M, ∀ l' ∈ M, ∀ P ∈ cov B g, j (l + l') P = j l (transl τ l' P) * j l' P

def IsMetric (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) (h : Pt E g → ℝ) : Prop :=
  ContDiffOn ℝ ∞ h (cov B g) ∧ (∀ P ∈ cov B g, 0 < h P) ∧
  ∀ l ∈ M, ∀ P ∈ cov B g, h (transl τ l P) * ‖j l P‖ ^ 2 = h P

def ChernIsFlat (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) : Prop :=
  ∀ P ∈ cov B g, ∀ v w : Pt E g, -ddc (fun Q => Real.log (h Q)) P v w = om0 τ P ![v, w]

def InducesPolarisation (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ) (M : Submodule ℤ (Fl g))
    (j : Fl g → Pt E g → ℂ) : Prop :=
  ∀ b ∈ B, ∃ f : Fl g → (Fin g → ℂ) → ℂ,
    (∀ l ∈ M, Differentiable ℂ (f l) ∧ ∀ z, j l (b, z) = Complex.exp (2 * π * Complex.I * f l z)) ∧
    ∀ l ∈ M, ∀ l' ∈ M, ∀ z,
      f l (z + per (τ b) l') + f l' z - f l' (z + per (τ b) l) - f l z = (riem l l' : ℂ)

end Family

def symMat (g : ℕ) : Submodule ℂ (Fin g → Fin g → ℂ) where
  carrier := {A | ∀ i j, A i j = A j i}
  add_mem' := fun {A B} hA hB i j => by simp [hA i j, hB i j]
  zero_mem' := fun _ _ => rfl
  smul_mem' := fun c A hA i j => by simp [hA i j]

def tauU {g : ℕ} (s : symMat g) : Matrix (Fin g) (Fin g) ℂ := Matrix.of s.1

def siegel (g : ℕ) : Set (symMat g) := {s | IsSiegel (tauU s)}

def symPart {g : ℕ} (A : Matrix (Fin g) (Fin g) ℂ) : symMat g :=
  ⟨fun i j => (A i j + A j i) / 2, fun i j => by simp only [add_comm]⟩

end GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
