import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsChartMemberP
import Development.AbelianVarietyTheory.Definitions.Divisors.OrdGeOfForall
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApproxOrbitSumsOfGaloisClassSums

noncomputable section

open IsLocalRing GlobalTheory.PolFan GlobalTheory.LocM

namespace GlobalTheory.Poinc.PreModel

section
variable {O : Type} [CommRing O] {bar : O → O} {q s : ℕ} {W : Matrix (Fin s) (Fin s) ℤ} {A : Type} [CommRing A] [IsLocalRing A]
  (Φ : VPre bar q W A)

theorem low_finite (y : Φ.Y) (P : (Fin s → Φ.X y) → Prop) (j : ℕ) :
    {mu | P mu ∧ ∑ i, qW W (Φ.δ y i) mu < (j : ℤ)}.Finite := by
  obtain ⟨c₀, hc₀, hq⟩ := GlobalTheory.Poinc.QWDom.qW_ge s W Φ.posW
  let D : LinearMap.BilinForm ℤ (Φ.X y) := ∑ i, Φ.δ y i
  have hD : ∀ x, D x x = ∑ i, Φ.δ y i x x := fun x => by simp [D, LinearMap.sum_apply]
  have hDs : ∀ a b, D a b = D b a := fun a b => by
    simp only [D, LinearMap.sum_apply]; exact Finset.sum_congr rfl fun i _ => (Φ.bal y i).1 a b
  have hDp : ∀ x, x ≠ 0 → 0 < D x x := fun x hx => by
    rw [hD]
    obtain ⟨i, hi⟩ := Φ.pos y x hx
    exact lt_of_lt_of_le hi (Finset.single_le_sum (f := fun i => Φ.δ y i x x) (fun i _ => Φ.nonneg y i x) (Finset.mem_univ i))
  refine (Set.Finite.pi' fun _ : Fin s => GlobalTheory.CompanionTheory.Ar.Fan.sublevel_finite _ D hDs hDp ⌈(j : ℝ) / c₀⌉).subset ?_
  rintro mu ⟨-, hmu⟩ u
  have h1 : ∀ i, c₀ * ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) ≤ (qW W (Φ.δ y i) mu : ℝ) := fun i =>
    hq _ (Φ.δ y i) (Φ.bal y i).1 (Φ.nonneg y i) mu
  have h2 : c₀ * ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) ≤ ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) := by
    have : ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) = ∑ i, ((∑ u, Φ.δ y i (mu u) (mu u) : ℤ) : ℝ) := by
      simp only [hD]; push_cast; exact Finset.sum_comm
    rw [this, Finset.mul_sum]; push_cast
    exact Finset.sum_le_sum fun i _ => by exact_mod_cast h1 i
  have h3 : (D (mu u) (mu u) : ℝ) ≤ ((∑ u, D (mu u) (mu u) : ℤ) : ℝ) := by
    exact_mod_cast Finset.single_le_sum (f := fun u => D (mu u) (mu u)) (fun u _ => by
      by_cases h : mu u = 0
      · simp [h]
      · exact (hDp _ h).le) (Finset.mem_univ u)
  have h4 : ((∑ i, qW W (Φ.δ y i) mu : ℤ) : ℝ) < j := by exact_mod_cast hmu
  have h5 : (D (mu u) (mu u) : ℝ) ≤ (j : ℝ) / c₀ := by
    rw [le_div_iff₀' hc₀]; nlinarith
  show D (mu u) (mu u) ≤ ⌈(j : ℝ) / c₀⌉
  exact_mod_cast h5.trans (Int.le_ceil _)

end

end GlobalTheory.Poinc.PreModel
