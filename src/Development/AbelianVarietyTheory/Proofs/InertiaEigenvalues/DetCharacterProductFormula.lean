import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.VacC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIntegralUnitDeterminantAtIdempotentResidue

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.ExportSeries GlobalTheory.ExportSeries.DualType
open Formalism.IndefR.Links (PolF)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

namespace GlobalTheory.TwistDetStab

open Classical

variable {D : D7}

theorem idemAt_mul_idem {Q : Finset (Pl D.host.E)} (h : SplitSet Q) {P : Pl D.host.E} (hP : P ∈ Q) :
    idemAt P * idem Q = idemAt P :=
  GlobalTheory.PlaceModelSum.mul_sum_orth (fun a ha => (h.isIdemAt ha).1) (fun a ha b hb hab => h.mul_eq_zero ha hb hab) hP

theorem idem_mul_self {Q : Finset (Pl D.host.E)} (h : SplitSet Q) : idem Q * idem Q = idem Q := by
  show (∑ P ∈ Q, idemAt P) * idem Q = idem Q
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun P hP => idemAt_mul_idem h hP

theorem idem_mul_idem_of_disjoint {Q s s' : Finset (Pl D.host.E)} (h : SplitSet Q) (hs : s ⊆ Q) (hs' : s' ⊆ Q)
    (hd : Disjoint s s') : idem s * idem s' = 0 := by
  rw [idem, idem, Finset.sum_mul_sum]
  exact Finset.sum_eq_zero fun i hi => Finset.sum_eq_zero fun j hj =>
    h.mul_eq_zero (hs hi) (hs' hj) fun e => Finset.disjoint_left.1 hd hi (e ▸ hj)

theorem val_mul (d e₁ e₂ : AE D) (h : e₁ * e₂ = 0) :
    (e₁ * d + (1 - e₁)) * (e₂ * d + (1 - e₂)) = (e₁ + e₂) * d + (1 - (e₁ + e₂)) := by
  linear_combination (d * d - 2 * d + 1) * h

theorem prod_val (d : AE D) {Q : Finset (Pl D.host.E)} (h : SplitSet Q) :
    ∀ s ⊆ Q, ∏ P ∈ s, (idemAt P * d + (1 - idemAt P)) = idem s * d + (1 - idem s) := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _; simp
  | insert a s ha ih =>
    intro hs
    rw [Finset.prod_insert ha, ih ((Finset.subset_insert a s).trans hs)]
    have e1 : idem (insert a s) = idemAt a + idem s := Finset.sum_insert ha
    rw [e1]
    refine val_mul d _ _ ?_
    have := idem_mul_idem_of_disjoint h (s := {a}) (s' := s)
      (Finset.singleton_subset_iff.2 (hs (Finset.mem_insert_self a s))) ((Finset.subset_insert a s).trans hs)
      (Finset.disjoint_singleton_left.2 ha)
    rwa [show idem ({a} : Finset (Pl D.host.E)) = idemAt a from Finset.sum_singleton _ _] at this

end GlobalTheory.TwistDetStab

end
