import Formalism.PeriodIntegrals.UpqRep

open MeasureTheory Matrix Finset Topology
open scoped InnerProductSpace ContDiff ComplexOrder

noncomputable section

namespace PI.UpqRep

section KF

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsKFin {n : ℕ} (ε : Fin n → Bool) (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (v : H) : Prop :=
  ∃ S : Submodule ℂ H, FiniteDimensional ℂ S ∧ v ∈ S ∧ IsKStableOn ε σ S

end KF

def thetaJ {n : ℕ} (ε : Fin n → Bool) (X : Matrix (Fin n) (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  -(Jm ε * Xᴴ * Jm ε)

def IsEquiv {n : ℕ} {H' H : Type} [NormedAddCommGroup H'] [InnerProductSpace ℂ H'] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] (ε : Fin n → Bool) (σ' : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H'))
    (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ U : H' ≃ₗᵢ[ℂ] H, ∀ g ∈ UJset ε, ∀ v : H', U (σ' g v) = σ g (U v)

def eI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨a.val, by omega⟩

def wI (k r : ℕ) (j : Fin (k + 1)) : Fin (2 * r + k + 1) := ⟨r + j.val, by omega⟩

def esI (k r : ℕ) (a : Fin r) : Fin (2 * r + k + 1) := ⟨2 * r + k - a.val, by omega⟩

def bvec {m : ℕ} (i : Fin m) : Fin m → ℂ := Pi.single i 1

def herm {ι : Type*} [Fintype ι] (H : Matrix ι ι ℂ) (v w : ι → ℂ) : ℂ := star w ⬝ᵥ (H *ᵥ v)

def inWb (k r : ℕ) (v : Fin (2 * r + k + 1) → ℂ) : Prop :=
  ∀ i : Fin (2 * r + k + 1), (i.val < r ∨ r + k < i.val) → v i = 0

def Tz (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) : ℝ := -(herm (Hpk k r) z z).re

def UWset (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) :
    Set (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :=
  {g | g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧ g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ z = z}

def blockW (k r : ℕ) (h : Matrix (Fin k) (Fin k) ℂ) :
    Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ :=
  fun i j =>
    if hi : r ≤ i.val ∧ i.val < r + k then
      (if hj : r ≤ j.val ∧ j.val < r + k then h ⟨i.val - r, by omega⟩ ⟨j.val - r, by omega⟩ else 0)
    else (if i = j then 1 else 0)

def IsFrameW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ)
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  g ∈ UH (Hpk k r) ∧
    (∀ a : Fin r, g *ᵥ bvec (eI k r a) = bvec (eI k r a) ∧
      g *ᵥ bvec (esI k r a) = bvec (esI k r a)) ∧
    g *ᵥ (((Real.sqrt (Tz k r z) : ℝ) : ℂ) • bvec (wI k r (Fin.last k))) = z

section Second

variable {k r : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def IsHCTypeW (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (u : Fin k → ℝ)
    (π : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) : Prop :=
  ∃ g, IsFrameW k r z g ∧ IsHCTypeU k u (fun h => π (g * blockW k r h * g⁻¹))

def InLieHpk (k r : ℕ) (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) : Prop :=
  Xᴴ * Hpk k r + Hpk k r * X = 0

def dsig (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H))
    (X : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (v : H) : H :=
  deriv (fun t : ℝ => σ (NormedSpace.exp ((t : ℂ) • X)) v) 0

def dsigW (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) :
    List (Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) → H → H
  | [], v => v
  | X :: w, v => dsig σ X (dsigW σ w v)

def IsLowUnitH (k r : ℕ) (ε : Fin (2 * r + k + 1) → Bool) (lam : Fin (2 * r + k + 1) → ℝ)
    (σ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (H →L[ℂ] H)) (w : H) : Prop :=
  ∃ P, IsCayleyU k r ε P ∧ IsLowUnit ε lam (fun g => σ (P⁻¹ * g * P)) w

end Second

end PI.UpqRep

end
