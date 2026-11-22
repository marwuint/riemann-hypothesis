import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.InfClassAt
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbLLMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsConstMeanLogAreaLogThetaNormLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbeddingsCurveFieldAboveFiniteNonempty
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RationalEqualSignKernelsLargeConstants
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConjugateTopBoundOfInputs

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField Matrix GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim GlobalTheory.TestLat

open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.SumSize GlobalTheory.KerConjMean

namespace GlobalTheory.KerConjMean

theorem sizes : ∀ (D : D7) (large₂ : SizeData₂ D) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 T : Type) (A : FamIn D.what₂.LL Γ Pl0 T D.R.m)
    (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A), HidaSetting large₂ R F →
    1 ≤ Real.log large₂.sc.b ∧ Real.log D.host.rdE ≤ Real.log large₂.sc.b ∧ |logDerivativeAtOne D| ≤ Real.log large₂.sc.b := by
  intro D large₂ Γ _ _ Pl0 T A Ks _ _ _ R F hS
  obtain ⟨-, hSz, -, -, -, -, -, -, -, hrd, hcond, -⟩ := hS.size
  have hb : Real.log large₂.sc.b = large₂.sc.x ^ large₂.sc.eps := by
    simp [Formalism.BasicNotions.Scale.b, Formalism.BasicNotions.Scale.L]
  have hL1 : 1 ≤ large₂.sc.x ^ large₂.sc.eps := Real.one_le_rpow large₂.sc.one_lt_alt.le large₂.sc.eps_pos.le
  have hqd : |large₂.logDerivativeAtOne| ≤ large₂.sc.x ^ large₂.sc.eps := hSz.2.2.2.2.2.2.1.2.2.2.2.2.1
  have he : large₂.logDerivativeAtOne = logDerivativeAtOne D := by
    rw [large₂.logDerivative_at_one_eq]
    rfl
  rw [hb]
  refine ⟨hL1, ?_, he ▸ hqd⟩
  have : Real.log D.host.rdE ≤ large₂.sc.L / 100 := hrd.trans hcond
  simp only [Formalism.BasicNotions.Scale.L] at this
  linarith

theorem meanInf_affine (K : Type) [Field K] [NumberField K] (a0 nD Gd : ℝ) (f g : InfinitePlace K → ℝ) (ha0 : 0 ≤ a0) :
    Formalism.PairingDivisionLocalBalance.meanInf K (fun v => a0 + nD * f v + Gd * g v) ≤
      2 * a0 + nD * Formalism.PairingDivisionLocalBalance.meanInf K f + Gd * Formalism.PairingDivisionLocalBalance.meanInf K g := by
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  have hn : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hc : (Fintype.card (InfinitePlace K) : ℝ) ≤ Module.finrank ℚ K := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank K
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces (K := K)
    exact_mod_cast (by omega : Fintype.card (InfinitePlace K) ≤ Module.finrank ℚ K)
  have h3 : 2 / (Module.finrank ℚ K : ℝ) * ((Fintype.card (InfinitePlace K) : ℝ) * a0) ≤ 2 * a0 := by
    rw [div_mul_eq_mul_div, div_le_iff₀ hn]
    nlinarith
  nlinarith [h3]

theorem exists_avg {α : Type} (S : Set α) (hS : S.Finite) (hne : S.Nonempty) (a0 nD Gd : ℝ) (h1 h2 : α → ℝ) :
    (∃ ρ ∈ S, a0 + nD * h1 ρ + Gd * h2 ρ ≤
      a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S)) ∧
    (∃ ρ ∈ S, a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) ≤
      a0 + nD * h1 ρ + Gd * h2 ρ) := by
  set s := hS.toFinset with hs
  have hsne : s.Nonempty := by rwa [hs, Set.Finite.toFinset_nonempty]
  have hcard : (Nat.card S : ℝ) = s.card := by
    rw [hs, Nat.card_eq_card_finite_toFinset hS]
  have hs1 : ∑ᶠ ρ ∈ S, h1 ρ = ∑ ρ ∈ s, h1 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hs2 : ∑ᶠ ρ ∈ S, h2 ρ = ∑ ρ ∈ s, h2 ρ := finsum_mem_eq_finite_toFinset_sum _ hS
  have hc0 : (0 : ℝ) < s.card := by exact_mod_cast hsne.card_pos
  set m := a0 + nD * ((∑ᶠ ρ ∈ S, h1 ρ) / Nat.card S) + Gd * ((∑ᶠ ρ ∈ S, h2 ρ) / Nat.card S) with hm
  have key : ∑ ρ ∈ s, (a0 + nD * h1 ρ + Gd * h2 ρ) = ∑ _ρ ∈ s, m := by
    rw [Finset.sum_const, nsmul_eq_mul, hm, hs1, hs2, hcard, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_const, nsmul_eq_mul]
    field_simp
  constructor
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.le
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩
  · obtain ⟨ρ, hρ, h⟩ := Finset.exists_le_of_sum_le hsne key.ge
    exact ⟨ρ, by rwa [hs, Set.Finite.mem_toFinset] at hρ, h⟩

end GlobalTheory.KerConjMean
end
