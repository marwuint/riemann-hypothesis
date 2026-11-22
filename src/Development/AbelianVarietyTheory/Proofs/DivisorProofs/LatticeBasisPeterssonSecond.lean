import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HermSysHypOneLeLambdaZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RatField
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AntitoneWeightLogBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FgIntOfForallIsIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegOfPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSmulNonnegLargeAtThreeFive
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSemilinearL2Independent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFrameDenominatorDominantWeightCm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowerCuspMultiplierGap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShortLatticeSpanningSets
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsShortGeneratorsOfShortSpanningFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PeterssonNormComponentAddLeOfGramFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightParameterStrictAntitone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnchoredWeightIndefiniteLiftGaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RunSizesQuotientGapsLarge
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DivLeSubMulDiv

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option maxHeartbeats 1000000

namespace GlobalTheory.HSShortRoad

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}

theorem antitone_of_gapGe {g : ℤ} (hg : 0 ≤ g) {la : AllWt.Weight Dw} (h : GapGe g la) (τ : Psi H) :
    Antitone (la τ) := by
  intro a i hai
  have h0 : ∀ k, 0 ≤ gap (la τ) k := fun k => by
    by_cases hk : k + 1 < Dw.p + Dw.q
    · exact hg.trans (h τ k hk)
    · rw [gap, dif_neg hk]
  have e := ofGaps_gap (la τ) a i
  have := Finset.sum_le_sum_of_subset_of_nonneg (f := gap (la τ)) (Finset.range_mono (show (a : ℕ) ≤ i from hai))
    fun k _ _ => h0 k
  rw [ofGaps] at e
  linarith

theorem gapGe_wt {P : WtPar Dw} (h : WtBig P) (j : ℕ) : GapGe (FlagTan.dimFlag Dw + 1) (P.wt j) := by
  have h₁ : GapGe (FlagTan.dimFlag Dw + 3) P.u₁ := h.gaps.mono (by
    push_cast
    exact le_mul_of_one_le_right (by positivity) (by omega))
  intro τ k hk
  have a := h₁ τ k hk
  have b := (P.gap_rem τ k).1
  have c : -2 ≤ gap (FlagTan.kap Dw τ) k := by rw [gap_kap τ hk]; split_ifs <;> omega
  have d : 0 ≤ gap (P.u₁ τ) k := le_trans (by positivity) a
  simp only [WtPar.wt, WtPar.uc, WtPar.u₂, Pi.add_apply, Pi.smul_apply, gap_add, gap_nsmul]
  nlinarith [mul_nonneg (Int.natCast_nonneg j) d, mul_nonneg (Int.natCast_nonneg (FlagTan.dimFlag Dw)) d]

noncomputable abbrev sz (la : AllWt.Weight Dw) : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)|

theorem one_le_sz {la : AllWt.Weight Dw} (h : 0 < sz la) : 1 ≤ sz la := by
  have e : sz la = ((∑ τ, ∑ k, |la τ k| : ℤ) : ℝ) := by push_cast; rfl
  rw [e] at h ⊢
  exact_mod_cast (show (0 : ℤ) < _ by exact_mod_cast h)

end Weights

theorem log_le_of_le_exp {s y : ℝ} (h0 : 0 ≤ s) (hy : 0 ≤ y) (h : s ≤ Real.exp y) : Real.log s ≤ y := by
  rcases h0.eq_or_lt with rfl | h0
  · simpa using hy
  · exact (Real.log_le_iff_le_exp h0).2 h

theorem log_size_le {a L κ s : ℝ} (ha : 0 < a) (hL : 1 ≤ L) (h₁ : Real.log a ≤ L) (hκ : 1 ≤ κ)
    (h₂ : Real.log κ ≤ 2 * L) (h0 : 0 ≤ s) (h : s ≤ 2 * ((a * L) ^ 2 * κ)) : Real.log s ≤ 10 * L := by
  have hp : 0 < 2 * ((a * L) ^ 2 * κ) := by positivity
  refine log_le_of_le_exp h0 (by linarith) (h.trans ((Real.log_le_iff_le_exp hp).1 ?_))
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity), Real.log_pow,
    Real.log_mul ha.ne' (by positivity)]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < L by linarith)
  push_cast
  linarith

theorem span_of_shortGen {F V κ : Type} [Field F] [NumberField F] [AddCommGroup V] [Module F V] [Module (𝓞 F) V]
    {Nm : κ → V → ℝ} {M : Submodule (𝓞 F) V} {n : ℕ} {w : Fin n → V} {Λ : ℝ} (h : CompHt.IsShortGen Nm M w Λ)
    (hM : Submodule.span F (M : Set V) = ⊤) : (∀ i, w i ∈ M) ∧ Submodule.span F (Set.range w) = ⊤ :=
  ⟨fun i => (h.gen _).2 (Submodule.subset_span ⟨i, rfl⟩), top_le_iff.1 (hM.ge.trans (Submodule.span_le.2 fun x hx =>
    Submodule.span_subset_span ℤ F _ ((h.gen x).1 hx)))⟩

theorem sum_univ_inst {α : Type} {i1 i2 : Fintype α} (f : α → ℝ) :
    @Finset.sum α ℝ _ (@Finset.univ α i1) f = @Finset.sum α ℝ _ (@Finset.univ α i2) f := by
  obtain rfl : i1 = i2 := Subsingleton.elim _ _
  rfl

theorem bound_le {C Z PP κ : ℝ} (hC : 0 ≤ C) (hZ : 1 ≤ Z) (hCZ : 6 * C ≤ Z) (hP : Z ^ 12 ≤ PP) (hκ : 1 ≤ κ) :
    C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) ≤ PP * κ := by
  have h5 : 0 ≤ Z ^ 5 := by positivity
  have e : C * (Z ^ 3 * (Z ^ 2 * κ) + Z ^ 5) = C * Z ^ 5 * (κ + 1) := by ring
  have a1 : C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := mul_le_mul_of_nonneg_left (by linarith) (by positivity)
  have a2 : 2 * C * Z ^ 5 ≤ Z * Z ^ 5 := mul_le_mul_of_nonneg_right (by linarith) h5
  have a3 : Z * Z ^ 5 ≤ Z ^ 12 := by
    rw [← pow_succ']
    exact pow_le_pow_right₀ hZ (by norm_num)
  have a4 : 2 * C * Z ^ 5 ≤ PP := a2.trans (a3.trans hP)
  rw [e]
  calc C * Z ^ 5 * (κ + 1) ≤ C * Z ^ 5 * (2 * κ) := a1
    _ = (2 * C * Z ^ 5) * κ := by ring
    _ ≤ PP * κ := mul_le_mul_of_nonneg_right a4 (by linarith)

end GlobalTheory.HSShortRoad
