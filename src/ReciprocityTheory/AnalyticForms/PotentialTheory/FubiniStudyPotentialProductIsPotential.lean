import ReciprocityTheory.AnalyticForms.PotentialTheory.ContDiffFubiniStudyRatioCompChart0
import ReciprocityTheory.AnalyticForms.PotentialTheory.HomogeneousLiftHolomorphicOnSnd

namespace ReciprocityTheory.AnForm.M

open MeasureTheory OnePoint CompatibleChartOperations

noncomputable section

def appendCLE (e e' : ℕ) : ((Fin e → ℂ) × (Fin e' → ℂ)) ≃L[ℂ] (Fin (e + e') → ℂ) :=
  ((LinearEquiv.sumArrowLequivProdArrow (Fin e) (Fin e') ℂ ℂ).symm.trans
    (LinearEquiv.funCongrLeft ℂ ℂ finSumFinEquiv.symm)).toContinuousLinearEquiv

def prodChart {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n) :
    OpenPartialHomeomorph (X × Y) (Fin (e + e') → ℂ) :=
  ((A.chart j).prod (B.chart k)).trans (appendCLE e e').toHomeomorph.toOpenPartialHomeomorph

section ProdChart

variable {e e' : ℕ} {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
  (A : FinHolAtlas e X) (B : FinHolAtlas e' Y) (j : Fin A.n) (k : Fin B.n)

end ProdChart

open scoped Classical in

def openAtlas {b : ℕ} (U : Set (Fin b → ℂ)) (hU : IsOpen U) (hne : U.Nonempty) :
    FinHolAtlas b U where
  n := 1
  chart _ :=
    { toFun := Subtype.val
      invFun := fun y => if h : y ∈ U then ⟨y, h⟩ else ⟨hne.some, hne.some_mem⟩
      source := Set.univ
      target := U
      map_source' := fun x _ => x.2
      map_target' := fun _ _ => Set.mem_univ _
      left_inv' := fun x _ => by simp [x.2]
      right_inv' := fun y hy => by simp [hy]
      open_source := isOpen_univ
      open_target := hU
      continuousOn_toFun := continuous_subtype_val.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_domRestrict]
        have : (U.domRestrict fun y => if h : y ∈ U then (⟨y, h⟩ : U) else ⟨hne.some, hne.some_mem⟩) =
            id := by
          funext y
          simp only [Set.domRestrict_apply, dif_pos y.2, id]
        rw [this]
        exact continuous_id }
  cover := fun _ => ⟨0, Set.mem_univ _⟩
  holo := by
    intro j k z ⟨hz, _⟩
    refine analyticAt_id.congr ?_
    filter_upwards [hU.mem_nhds hz] with y hy
    simp [hy]

open scoped Classical in

def diagSec (x y : OnePoint ℂ × OnePoint ℂ) : ℂ :=
  if x.1 = ∞ then
    (if x.2 = ∞ then crd1 y.1 - crd1 y.2 else crd1 y.1 * crd0 y.2 - 1)
  else
    (if x.2 = ∞ then 1 - crd0 y.1 * crd1 y.2 else crd0 y.2 - crd0 y.1)

end

end ReciprocityTheory.AnForm.M
