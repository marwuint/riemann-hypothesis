import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfBoundedContinuousInvariant

noncomputable section

open MeasureTheory Set GlobalTheory.AutomorphicL2Unitary
open scoped ENNReal Pointwise

namespace GlobalTheory.Cusp.Model

section Four

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def four (D : D7) : HSp D := Examples₂.stdSpace Examples₂.star_isIntegral 4 ![false, false, true, true] 2 2

theorem isIsoSub_four (D : D7) :
    IsIsoSub (four D) (i := 2) (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) := by
  refine ⟨?_, ?_⟩
  · refine Fintype.linearIndependent_iff.2 fun g h => ?_
    have h' : ∑ i : Fin 2, g i • (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E).transpose i =
      (0 : Fin 4 → D.host.E) := h
    have h0 := congrFun h' 0
    have h1 := congrFun h' 1
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · simpa [Fin.sum_univ_two] using h0
    · simpa [Fin.sum_univ_two] using h1
  · have hg : ∀ i j : Fin 4, (four D).gram i j =
        if i = j then (Examples₂.sgn (![false, false, true, true] i) : D.host.E) else 0 :=
      Examples₂.stdSpace_gram_apply Examples₂.star_isIntegral 4 ![false, false, true, true] 2 2
    funext a b
    change ∑ j : Fin 4, (∑ i : Fin 4, D.sp.cm.sig ((!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) i a) *
      (four D).gram i j) * (!![1, 0; 0, 1; 1, 0; 0, 1] : Matrix (Fin 4) (Fin 2) D.host.E) j b = 0
    fin_cases a <;> fin_cases b <;> simp [Fin.sum_univ_four, hg, Examples₂.sgn]

theorem k_columnFlag_four (D : D7) : (columnFlag (isIsoSub_four D)).k = 2 := rfl

end Four

end GlobalTheory.Cusp.Model

end
