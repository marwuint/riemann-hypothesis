import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.AlgebraMapAEEqZero
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.InfPartOfSplitIdem
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitOrInertP
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.PlaceFinal
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.SplitLinF

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.IndefR.Datum
open scoped TensorProduct

namespace Formalism.IndefR.Fin.LevelGroupLemmas

open Formalism.IndefR.Fin.LevelGroupLemmas.Lat

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def epsP (P : Finset (Formalism.L2.DIV.Pl D.host.E)) : AF D.host.F := ∑ PP ∈ P, sA (belowPl PP) 1

theorem sA_orth' {v w : HeightOneSpectrum (𝓞 D.host.F)} (h : v ≠ w) :
    sA v (1 : v.adicCompletion D.host.F) * sA w (1 : w.adicCompletion D.host.F) = 0 :=
  algebraMap_AE_eq_zero (D := D) (by rw [map_mul]; exact phiE_orth h)

section Sum

variable {P : Finset (Formalism.L2.DIV.Pl D.host.E)} {e : AE D} {es : Formalism.L2.DIV.Pl D.host.E → AE D}

theorem algebraMap_epsP (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP) :
    algebraMap (AF D.host.F) (AE D) (epsP P) = e + cA D e := by
  rw [epsP, map_sum, he, map_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun PP hPP => (below_of_idemAt (hes PP hPP)).symm

open Classical in
theorem single_one_mul_idempotent_eq_zero_of_notMem (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) {a : Formalism.L2.DIV.Pl D.host.E} {A : Finset (Formalism.L2.DIV.Pl D.host.E)} (ha : a ∉ A)
    (hsub : insert a A ⊆ P) : sA (belowPl a) (1 : (belowPl a).adicCompletion D.host.F) * epsP A = 0 := by
  rw [epsP, Finset.mul_sum]
  refine Finset.sum_eq_zero fun PP hPP => sA_orth' fun hv => ?_
  have := idemSum_below_inj hes he hc (hsub (Finset.mem_insert_self a A)) (hsub (Finset.mem_insert_of_mem hPP)) hv
  exact ha (this ▸ hPP)

theorem isIdempotentElem_placeIdempotent (hes : ∀ PP ∈ P, Formalism.L2.NTheta.IsIdemAt (es PP) PP) (he : e = ∑ PP ∈ P, es PP)
    (hc : e * cA D e = 0) : ∀ A : Finset (Formalism.L2.DIV.Pl D.host.E), A ⊆ P → IsIdempotentElem (epsP A) := by
  classical
  intro A
  induction A using Finset.induction_on with
  | empty => intro _; simp [epsP, IsIdempotentElem]
  | insert a A ha ih =>
    intro hsub
    rw [epsP, Finset.sum_insert ha]
    exact isIdem_add_orth (sA_idem _) (ih ((Finset.subset_insert a A).trans hsub))
      (single_one_mul_idempotent_eq_zero_of_notMem hes he hc ha hsub)

end Sum

theorem vacFixOff (hSL : SplitLin D) (hPM : PlaceModelAt D) (hSOI : SplitOrInert D) : VacFixOffO D :=
  vacFixOff_of hSL hPM hSOI fun _ _ _ _ _ _ _ _ hfS hfT _ _ _ _ hg hh t => actO_mem_latAll_iff hfS hfT hg hh t

end Formalism.IndefR.Fin.LevelGroupLemmas

namespace Formalism.IndefR.Fin

end Formalism.IndefR.Fin

end
