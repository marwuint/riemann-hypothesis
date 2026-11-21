import Mathlib
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.PrincipalRootReZeroImSq
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Polynomial
open scoped TensorProduct Pointwise

namespace GlobalTheory.CM

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

theorem baseChange_neg_form (D : Datum H) (x y : ℝ ⊗[ℤ] D.La) :
    (-D.EF).baseChange ℝ x y = -D.EF.baseChange ℝ x y := by
  induction x with
  | zero => simp
  | add a b ha hb => simp only [map_add, LinearMap.add_apply, ha, hb]; ring
  | tmul r a =>
    induction y with
    | zero => simp
    | add a b ha hb => simp only [map_add, ha, hb]; ring
    | tmul s b => simp

def oppDatum (D : Datum H) : Datum H where
  La := D.La
  fin := D.fin
  proj := D.proj
  EF := -D.EF
  alt x := by simp [D.alt]
  unimod := by
    have : (⇑(-D.EF) : D.La → _) = (fun f => -f) ∘ D.EF := rfl
    rw [this]
    exact neg_involutive.bijective.comp D.unimod
  adj a x y := by simp [D.adj]
  p := D.q
  q := D.p
  rank := by rw [D.rank, add_comm]
  dom := by
    obtain ⟨J, h1, h2, h3, h4⟩ := D.dom
    refine ⟨-J, fun x => by simp [h1], fun x y => ?_, fun x hx => ?_, fun a A t hA ht => ?_⟩
    · simp [baseChange_neg_form, h2]
    · simpa [baseChange_neg_form] using h3 x hx
    · obtain ⟨e1, e2, e3⟩ := h4 a A (starRingEnd ℂ t) hA (by
        rw [ht, map_sum]
        refine Finset.sum_congr rfl fun τ _ => ?_
        simp [add_comm])
      refine ⟨by rw [LinearMap.neg_comp, LinearMap.comp_neg, e1], by simpa using e2, ?_⟩
      rw [LinearMap.neg_comp, map_neg, e3]
      simp

@[simp] theorem oppDatum_p (D : Datum H) : (oppDatum D).p = D.q := rfl

@[simp] theorem oppDatum_q (D : Datum H) : (oppDatum D).q = D.p := rfl

end General

namespace CyclotomicTwentyEight

abbrev CyclotomicFieldTwentyEight : Type := CyclotomicField 28 ℚ

instance isCyclotomicExtension_cyclotomicField28 : IsCyclotomicExtension {28} ℚ CyclotomicFieldTwentyEight := CyclotomicField.isCyclotomicExtension 28 ℚ

instance isCMField_cyclotomicField28 : IsCMField CyclotomicFieldTwentyEight := IsCyclotomicExtension.Rat.isCMField CyclotomicFieldTwentyEight (S := {28}) ⟨28, rfl, by norm_num⟩

end CyclotomicTwentyEight

end GlobalTheory.CM
