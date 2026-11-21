import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.ChartChg
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfCongrJet
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonOfProdLinear

set_option autoImplicit false

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB

namespace GlobalTheory.SymbolCols

theorem colM_apply {ι : Type} [Finite ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) (b : Fin n) (l : ι) :
    colM m b l = m (l, b) := by
  simp [colM]

theorem sum_degree_colM {ι : Type} [Fintype ι] {n : ℕ} (m : ι × Fin n →₀ ℕ) :
    ∑ b, (colM m b).degree = m.degree := by
  simp only [Finsupp.degree_eq_sum, colM_apply]
  rw [Fintype.sum_prod_type, Finset.sum_comm]

theorem coeff_mul_congr {k σ : Type} [CommRing k] (N : ℕ) (f g E : MvPowerSeries σ k)
    (h : ∀ mo : σ →₀ ℕ, mo.degree ≤ N → coeff mo f = coeff mo g)
    (mo : σ →₀ ℕ) (hmo : mo.degree ≤ N) : coeff mo (f * E) = coeff mo (g * E) := by
  classical
  rw [coeff_mul, coeff_mul]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hp' : p.1 + p.2 = mo := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  have hd : p.1.degree + p.2.degree = mo.degree := by rw [← hp', map_add]
  rw [h p.1 (by omega)]

theorem exists_col {ι : Type} [Fintype ι] {n : ℕ} (m a : ι × Fin n →₀ ℕ)
    (hdeg : m.degree = a.degree) (hne : m ≠ a) :
    ∃ b, (colM m b).degree ≤ (colM a b).degree ∧ colM m b ≠ colM a b := by
  by_contra hcon
  push Not at hcon
  have hle : ∀ b, (colM a b).degree ≤ (colM m b).degree := fun b => by
    by_contra h
    have := hcon b (by omega)
    rw [this] at h
    exact h le_rfl
  have hs : ∑ b, (colM a b).degree = ∑ b, (colM m b).degree := by
    rw [sum_degree_colM, sum_degree_colM, hdeg]
  have heq := (Finset.sum_eq_sum_iff_of_le fun b _ => hle b).1 hs
  refine hne (Finsupp.ext fun ⟨l, b⟩ => ?_)
  rw [← colM_apply, ← colM_apply, hcon b (heq b (Finset.mem_univ b)).ge]

end GlobalTheory.SymbolCols

namespace GlobalTheory

end GlobalTheory
