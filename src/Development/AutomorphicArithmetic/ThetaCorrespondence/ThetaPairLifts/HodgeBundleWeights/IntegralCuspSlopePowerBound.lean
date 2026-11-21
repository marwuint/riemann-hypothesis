import Mathlib
import Development.AutomorphicArithmetic.ThetaCorrespondence.FockModels.TamagawaPeterssonLambdaSqNonneg
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
namespace UpperTheory.Lit.Tam
end UpperTheory.Lit.Tam
namespace GlobalTheory.SupModel
end GlobalTheory.SupModel
namespace GlobalTheory.LevGeo.RankBd
end GlobalTheory.LevGeo.RankBd
namespace GlobalTheory.LamPet
end GlobalTheory.LamPet
namespace GlobalTheory.LamMuMax
end GlobalTheory.LamMuMax
namespace GlobalTheory
end GlobalTheory
namespace GlobalTheory
end GlobalTheory
namespace GlobalTheory.BergComp
end GlobalTheory.BergComp
namespace GlobalTheory.ConstSzRows
end GlobalTheory.ConstSzRows
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
namespace GlobalTheory.BergRank
end GlobalTheory.BergRank
namespace GlobalTheory.BergRank
theorem _root_.UpperTheory.Lit.Tam.tamagawa_number_formula : _root_.GlobalTheory.CovTop.PublishedHodgeBundleTheorems → ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ j : ℕ, 1 ≤ (T.Q.Dw j).p → 1 ≤ (T.Q.Dw j).q → 2 < Module.finrank ℚ D.host.E / 2 → InR D j → ∀ (Y : Deep T.toCore j) (e : ℕ) (o : ℝ), Y.Good e o → ∀ Lb : ℝ, 1 ≤ Lb → Real.log Y.d.l₂.M ≤ 30 * Lb → fieldSz D.host.E ≤ 3 * Lb → Real.log (D.R.f * D.R.r) ≤ Lb → o ≤ 391 * (D.R.f * D.R.r * Lb) ^ 2 → ∀ la : AllWt.Weight (T.Q.Dw j), (∀ τ, Antitone (la τ)) → Real.log (∑ τ, ∑ k, |(la τ k : ℝ)|) ≤ 20 * Lb → ∀ Z, BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ SupBdWt Y.U (xiR D) (fun _ => D.sp.W j) Y.dict Z la (Real.exp (C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) ∧ Real.log (Y.rkC la Z) ≤ C * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by
  intro hP
  refine ⟨4000, by norm_num, ?_⟩
  intro D T hT j hp hq hE hj Y e o hY Lb hLb hM hsz hfr ho la hla hS Z
  have hL := (GlobalTheory.T.deepLevelCover_principalLevel_laws_galois D T j Y e o hT hj hY hY.unit hY.modelW).1
  set S : ℝ := ∑ τ, ∑ k, |(la τ k : ℝ)| with hSdef
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
  set n : ℝ := (Module.finrank ℚ D.host.E : ℝ) with hn
  have hn1 : 1 ≤ n := by
    have : 0 < Module.finrank ℚ D.host.E := Module.finrank_pos
    rw [hn]; exact_mod_cast this
  have hnlog : Real.log n ≤ 3 * Lb := (log_finrank_le_fieldSz _).trans hsz
  set w : ℝ := 2 * n * S + 1 with hw
  have hnS : 0 ≤ n * S := mul_nonneg (by linarith) hS0
  have hw1 : 1 ≤ w := by rw [hw]; nlinarith
  have hlogw : Real.log w ≤ 25 * Lb := by
    have hint : S = (((∑ τ, ∑ k, |la τ k|) : ℤ) : ℝ) := by rw [hSdef]; push_cast; rfl
    have hz : (0 : ℤ) ≤ ∑ τ, ∑ k, |la τ k| := Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _
    rcases hz.eq_or_lt with h0 | h1
    · have : S = 0 := by rw [hint, ← h0]; simp
      rw [hw, this]; simp; linarith
    · have hS1 : 1 ≤ S := by rw [hint]; exact_mod_cast h1
      have hwle : w ≤ 3 * (n * S) := by rw [hw]; nlinarith
      have hlS : Real.log S ≤ 20 * Lb := hS
      have e1 : Real.log w ≤ Real.log (3 * (n * S)) := Real.log_le_log (by linarith) hwle
      rw [Real.log_mul (by norm_num) (by positivity), Real.log_mul (by positivity) (by positivity)] at e1
      have h3 : Real.log 3 < 2 := by
        have := Real.log_two_lt_d9; have h4 : Real.log 3 < Real.log 4 := Real.log_lt_log (by norm_num) (by norm_num)
        have : Real.log 4 = 2 * Real.log 2 := by rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
        linarith
      linarith
  obtain ⟨hβ1, hβ⟩ := UpperTheory.Lit.Tam.supConst2Bounds D Y.d.l₂.M Lb w (by have := Y.d.l₂.three_le; omega) hLb hM hsz hfr hw1 hlogw
  set β := MainStatements.Tam.Plug.supConst2 D.host.E D.R.r D.host.d Y.d.l₂.M w with hβdef
  have hβexp : β ≤ Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3) := by
    rw [← Real.exp_log (by linarith : 0 < β)]; exact Real.exp_le_exp.2 hβ
  have hsp : ∀ σ k, ∑ τ, ((Y.U σ).X k).spread (AllWt.modelWt (Y.U σ) (wtOf _ la 0) k) τ ≤ w := fun σ k =>
    (sum_spread_modelWt_le _ la k).trans (by rw [hw]; linarith)
  have hB : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la β := fun σ hσ y hy =>
    UpperTheory.Lit.Tam.tamagawaPeterssonLambdaSq_nonneg trivial D j _ _ _ _ _ Y.U Y.dict hL σ hσ (wtOf _ la 0) (AllWt.even_wtOf la 0) w (by linarith) (hsp σ) Z y hy
  have hBexp : BergLe Z Y.U (fun _ => D.sp.W j) Y.dict la (Real.exp (4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3)) :=
    fun σ hσ y hy => (hB σ hσ y hy).trans (ENNReal.ofReal_le_ofReal hβexp)
  refine ⟨hBexp, ?_, ?_⟩
  · refine SupBdWt.of_bergOn (Real.exp_pos _).le ?_ hBexp
    intro σ hσ g
    obtain ⟨th, hr, -, hd⟩ := hY.dictU σ hσ
    exact Formalism.L2.Pj.dict_dom_of hd g
  · have hrk := _root_.GlobalTheory.RankBergman.rkC_le_of_bergLe D T.toCore j Y e o hY la Z β (by linarith) hB
    have hpos : 0 ≤ 4000 * ((D.R.f : ℝ) * D.R.r * Lb) ^ 3 := by positivity
    rcases (show (0 : ℝ) ≤ Y.rkC la Z by unfold Deep.rkC; positivity).eq_or_lt with h0 | h0
    · rw [← h0, Real.log_zero]; exact hpos
    · exact (Real.log_le_log h0 hrk).trans hβ
end GlobalTheory.BergRank
end
namespace GlobalTheory.CovTop.LamCore
end GlobalTheory.CovTop.LamCore
end
