import Mathlib

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Complex Filter
open NumberField.InfinitePlace.Completion
open scoped ContDiff Classical

namespace PI.CuspInfChar

section matrices
variable {A B : Type} [CommRing A] [CommRing B] {n : ℕ}

abbrev GlobalTheory (n i : ℕ) : Type := {p : Fin n × Fin n // p.1.val < i ∧ i ≤ p.2.val}

def blk {i : ℕ} (x : GlobalTheory n i → A) : Matrix (Fin n) (Fin n) A :=
  of fun a b => if h : a.val < i ∧ i ≤ b.val then x ⟨(a, b), h⟩ else 0
theorem blk_mul {i : ℕ} (x y : GlobalTheory n i → A) : blk x * blk y = 0 := by
  ext a b; rw [mul_apply]; refine Finset.sum_eq_zero fun c _ => ?_
  by_cases h : c.val < i <;> simp [blk, h]

def uni {i : ℕ} (x : GlobalTheory n i → A) : GL (Fin n) A :=
  ⟨1 + blk x, 1 - blk x, by simp [add_mul, mul_sub, blk_mul], by simp [mul_add, sub_mul, blk_mul]⟩

def dia (i : ℕ) (t : Aˣ) : GL (Fin n) A :=
  ⟨diagonal fun a => if a.val < i then t else 1, diagonal fun a => if a.val < i then ↑t⁻¹ else 1,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; ext a; split_ifs <;> simp,
    by rw [diagonal_mul_diagonal, ← diagonal_one]; congr; ext a; split_ifs <;> simp⟩
end matrices

variable (F : Type) [Field F] [NumberField F]

abbrev Ad := AdeleRing (𝓞 F) F
abbrev Pl := HeightOneSpectrum (𝓞 F)

abbrev G (n : ℕ) := GL (Fin n) (Ad F)
instance (n i : ℕ) : MeasurableSpace (GlobalTheory n i → Ad F) := borel _
variable {F} {n : ℕ}

structure IsCuspForm (φ : G F n → ℂ) : Prop where
  cont : Continuous φ
  inv : ∀ (γ : GL (Fin n) F) g, φ (GeneralLinearGroup.map (algebraMap F (Ad F)) γ * g) = φ g
  cen : ∀ z : (Ad F)ˣ, ∃ c : ℂ, ∀ g, φ (dia n z * g) = c * φ g
  bdd : ∃ C, ∀ g, ‖φ g‖ ≤ C
  cusp : ∀ i, 0 < i → i < n → ∀ (μ : Measure (GlobalTheory n i → Ad F)) [μ.IsAddHaarMeasure] (D : Set (GlobalTheory n i → Ad F)),
    IsAddFundamentalDomain (AddSubgroup.pi Set.univ fun _ : GlobalTheory n i => AdeleRing.principalSubgroup (𝓞 F) F) D μ →
    ∀ g, ∫ x in D, φ (uni x * g) ∂μ = 0
  ne : φ ≠ 0

variable (F) in

structure Form where
  n : ℕ
  pos : 0 < n
  φ : G F n → ℂ
  cusp : IsCuspForm φ

end PI.CuspInfChar

end
