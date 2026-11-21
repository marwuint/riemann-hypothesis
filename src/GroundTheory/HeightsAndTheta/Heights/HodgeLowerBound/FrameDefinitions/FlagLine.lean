import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.HasCoverByOne
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree.Line

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

def colRestrict {s : ℕ} (A : Fin s → Fin 2) : (Fin 2 → Ω) →ₗ[Ω] (Fin s → Ω) where
  toFun w a := w (A a)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

def coordFun (s : ℕ) (m : Fin 2) : Module.Dual Ω (⋀[Ω]^s (Fin 2 → Ω)) :=
  exteriorPower.alternatingMapLinearEquiv
    ((Matrix.detRowAlternating (n := Fin s) (R := Ω)).compLinearMap (colRestrict fun _ => m))

theorem coordFun_one (m : Fin 2) (v : Fin 1 → Fin 2 → Ω) :
    coordFun 1 m (exteriorPower.ιMulti Ω 1 v) = v 0 m := by
  simp only [coordFun, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti,
    AlternatingMap.compLinearMap_apply]
  change Matrix.det (Matrix.of fun i => (colRestrict fun _ => m) (v i)) = _
  rw [Matrix.det_unique]
  rfl

def pick (A : Fin 1 → Fin 2) (m : Fin 2) : Ω := if m = A 0 then 1 else 0

theorem pick_mem (c : Unit → Fin 2) (A : Fin 1 → Fin 2) (m : Fin 2) :
    (1 : Ω) ^ 0 * pick A m ∈ chartRing ℤ (segreCoord yLine) c := by
  unfold pick
  split_ifs
  · simp
  · simp

theorem pick_sum (c : Unit → Fin 2) (A A' : Fin 1 → Fin 2) :
    ∑ m : Fin 2, pick A m * (coordFun 1 m (exteriorPower.ιMulti Ω 1 (⇑(Pi.basisFun Ω (Fin 2)) ∘ A')) *
      chartMono yLine c (-0)) = if A' = A then 1 else 0 := by
  simp only [coordFun_one, chartMono, neg_zero, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one,
    Function.comp_apply, Pi.basisFun_apply, pick]
  have hAA : A' = A ↔ A' 0 = A 0 := ⟨fun h => h ▸ rfl, fun h => funext fun a => by
    rw [Fin.fin_one_eq_zero a]; exact h⟩
  by_cases h : A' 0 = A 0
  · rw [if_pos (hAA.2 h), h]
    simp [Pi.single_apply]
  · rw [if_neg (fun h' => h (hAA.1 h'))]
    simpa [Pi.single_apply] using h

def linePl (II : IntersectionSystem)
    (hII : ∀ W : Ideal (MRing (PBlk 2)), IsArithVar W 1 → 0 ≤ II Unit (PBlk 2) W 1 ![fsLine 2]) :
    PlueckerData (lineData II hII) where
  e _ := ⇑(Pi.basisFun Ω (Fin 2))
  e_indep _ := (Pi.basisFun Ω (Fin 2)).linearIndependent
  e_span _ := (Pi.basisFun Ω (Fin 2)).span_eq
  M _ _ := 2
  M_ge _ i := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    show Nat.choose 2 1 ≤ 2
    decide
  bdeg _ _ := 0
  gen _ i m := coordFun _ m
  global _ i m c _ v hv := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    show coordFun 1 m (exteriorPower.ιMulti Ω 1 v) * chartMono yLine c (-0) ∈
      chartRing ℤ (segreCoord yLine) c
    rw [coordFun_one]
    simp only [chartMono, neg_zero, Pi.zero_apply, zpow_zero, Finset.prod_const_one, mul_one]
    exact mem_trivLat.1 (hv 0) m
  generates _ i c _ := by
    obtain ⟨i, hi⟩ := i
    obtain rfl : i = 0 := by change i < 1 at hi; omega
    refine hasCoverBy_one _ _ ⟨⇑(Pi.basisFun Ω (Fin 2)), isFrameOver_line (c ()),
      (Pi.basisFun Ω (Fin 2)).span_eq, fun A _ => ⟨pick A, fun m => ⟨0, pick_mem c A m⟩,
        fun A' _ => pick_sum c A A'⟩⟩
  wdeg _ := 0
  ω _ := exteriorPower.ιMulti Ω 2 ⇑(Pi.basisFun Ω (Fin 2))
  detW _ c _ := hasCoverBy_one _ _ ⟨⇑(Pi.basisFun Ω (Fin 2)), isFrameOver_line (c ()),
    (Pi.basisFun Ω (Fin 2)).span_eq, 1, isUnitOn_one _ _ _, by simp [chartMono]; rfl⟩

end GroundTheory.Heights₂.Heights.LowerBoundFree.Line
