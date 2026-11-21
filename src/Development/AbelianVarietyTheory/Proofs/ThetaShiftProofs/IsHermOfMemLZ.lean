import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FourierCoefficientSupportHolds
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FixedPointImaginarySpan

namespace GlobalTheory.MaxCusp

open NumberField Complex MeasureTheory Matrix ReciprocityTheory.ChartRestriction.G.FD
open scoped ComplexConjugate

noncomputable section

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r d : ℕ}

def IsIsoFam (G : Matrix (Fin r) (Fin r) E) (u : Fin d → Fin r → E) : Prop :=
  (∀ i k, herm G (u i) (u k) = 0) ∧ LinearIndependent E u

def IsHerm {ι : Type} (b : ι → Fin d → Fin d → ℂ) : Prop := ∀ τ i k, b τ k i = conj (b τ i k)

variable (X : Data E r)

def zmat (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (τ : X.Ψ) :
    Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun a j => (if a = j then 1 else 0) -
    I * X.c τ * ∑ i, ∑ k, b τ i k * Data.emb τ.1 (u i) a *
      ∑ l, τ.1 (X.Gm j l) * conj (Data.emb τ.1 (u k) l)

def Zb (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) : Frame X.Ψ r :=
  fun τ => (zmat X u b τ * mat x τ : Matrix (Fin r) (Fin r) ℂ)

def pairR (χ b : X.Ψ → Fin d → Fin d → ℂ) : ℝ := (∑ τ, ∑ i, ∑ k, χ τ i k * b τ i k).re

def embH (β : Matrix (Fin d) (Fin d) E) : X.Ψ → Fin d → Fin d → ℂ := fun τ i k => τ.1 (β i k)

def LZ (d g : ℕ) : Set (X.Ψ → Fin d → Fin d → ℂ) :=
  {b | ∃ β : Matrix (Fin d) (Fin d) E, (∀ i k, cc (β i k) = β k i) ∧
    (∀ i k, ∃ γ : E, IsIntegral ℤ γ ∧ β i k = ((g * dEnat E : ℕ) : E) / 2 * γ) ∧ b = embH X β}

def IsFreqZ (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  ∀ b ∈ LZ X d g, ∃ k : ℤ, 2 * pairR X χ b = k

def IsLZBasis (g : ℕ) (ω : Fin (d * d * Fintype.card X.Ψ) → X.Ψ → Fin d → Fin d → ℂ) : Prop :=
  (∀ j, ω j ∈ LZ X d g) ∧
    (∀ b ∈ LZ X d g, ∃! n : Fin (d * d * Fintype.card X.Ψ) → ℤ, b = ∑ j, (n j : ℂ) • ω j) ∧
    LinearIndependent ℝ ω

open Classical in

def fz (u : Fin d → Fin r → E) (g : ℕ) (χ : X.Ψ → Fin d → Fin d → ℂ) (G : Frame X.Ψ r → ℂ)
    (x : Frame X.Ψ r) : ℂ :=
  if IsHerm χ ∧ IsFreqZ X g χ then
    if h : ∃ ω, IsLZBasis (d := d) X g ω then
      ∫ t in Set.pi Set.univ (fun _ : Fin (d * d * Fintype.card X.Ψ) => Set.Icc (0 : ℝ) 1),
        G (Zb X u (∑ j, (t j : ℂ) • h.choose j) x) *
          cexp (-(4 * Real.pi * I) * pairR X χ (∑ j, (t j : ℂ) • h.choose j))
    else 0
  else 0

def chiAt (χ : X.Ψ → Fin d → Fin d → ℂ) (a : X.Ψ → Fin d → ℂ) (τ : X.Ψ) : ℂ :=
  ∑ i, ∑ k, χ τ i k * a τ i * conj (a τ k)

section Two

theorem isIsoFam_two (G : Matrix (Fin r) (Fin r) E) (u : Fin 2 → Fin r → E) :
    IsIsoFam G u ↔ IsIsoPair G u := Iff.rfl
theorem Zb_two (u : Fin 2 → Fin r → E) : Zb X u = X.Zb u := rfl
theorem LZ_two (g : ℕ) : LZ X 2 g = X.LZ g := rfl
theorem isFreqZ_two (g : ℕ) : IsFreqZ (d := 2) X g = X.IsFreqZ g := rfl
theorem fz_two (u : Fin 2 → Fin r → E) (g : ℕ) : fz X u g = X.fz u g := rfl
theorem chiAt_two : chiAt (d := 2) X = X.chiAt := rfl

end Two

theorem mat_Zb (u : Fin d → Fin r → E) (b : X.Ψ → Fin d → Fin d → ℂ) (x : Frame X.Ψ r) (τ : X.Ψ) :
    mat (Zb X u b x) τ = zmat X u b τ * mat x τ := rfl

theorem embH_add (β β' : Matrix (Fin d) (Fin d) E) : embH X (β + β') = embH X β + embH X β' := by
  funext τ i k; simp [embH]

end

end GlobalTheory.MaxCusp
