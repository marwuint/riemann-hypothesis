import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeStabiliserIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AutomorphicInstanceExistsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicUnitaryHaarBiInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AestronglyMeasurableCompRep
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsWeakIntegralOfStronglyContinuous
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsCompleteDense

open MeasureTheory Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField Matrix
open scoped InnerProductSpace ComplexOrder Classical

namespace GlobalTheory.Mem.RowsBundle

section Infl

variable {I : AutInst} {g : ℕ} {Q : Type} [Group Q] (ρ : Red I g Q)

theorem fibre_eq (q : Q) :
    ∃ t : I.Gf, {x | x ∈ I.Kset ∧ ρ.toFun x = q} = (fun y => t * y) ⁻¹' I.Kg g := by
  obtain ⟨t, ht, rfl⟩ := ρ.surj q
  have ht' : t⁻¹ ∈ I.Kset := (Ksub I).inv_mem ht
  refine ⟨t⁻¹, Set.ext fun x => ⟨fun h => ?_, fun h => ?_⟩⟩
  · refine (ρ.ker _ ((Ksub I).mul_mem ht' h.1)).1 ?_
    rw [ρ.map_mul _ ht' _ h.1, ρ.map_inv ht, h.2, inv_mul_cancel]
  · have h1 : t⁻¹ * x ∈ I.Kset := h.1
    have hx : x ∈ I.Kset := ((Ksub I).mul_mem_cancel_left ht').1 h1
    have h2 := (ρ.ker _ h1).2 h
    rw [ρ.map_mul _ ht' _ hx, ρ.map_inv ht, inv_mul_eq_one] at h2
    exact ⟨hx, h2.symm⟩

theorem integral_inflate [Fintype Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (F : Q → ℂ) :
    Integrable (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) μf ∧
      ∫ x, (if x ∈ I.Kset then F (ρ.toFun x) else 0) ∂μf = ((μf (I.Kg g)).toReal : ℂ) * ∑ q, F q := by
  have hU : IsOpen (I.Kg g) := I.topf_open g hg
  have hfin : μf (I.Kg g) ≠ ⊤ :=
    ((measure_mono fun x hx => hx.1).trans_lt (GlobalTheory.adelicStab_isCompact_isOpen I).1.measure_lt_top).ne
  have hm : ∀ q, MeasurableSet {x | x ∈ I.Kset ∧ ρ.toFun x = q} ∧
      μf {x | x ∈ I.Kset ∧ ρ.toFun x = q} = μf (I.Kg g) := fun q => by
    obtain ⟨t, ht⟩ := fibre_eq ρ q
    rw [ht]
    exact ⟨(hU.preimage (by fun_prop)).measurableSet, measure_preimage_mul μf t _⟩
  have e : (fun x => if x ∈ I.Kset then F (ρ.toFun x) else 0) =
      fun x => ∑ q, {x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q) x := by
    funext x
    by_cases hx : x ∈ I.Kset
    · rw [if_pos hx, Finset.sum_eq_single (ρ.toFun x)]
      · rw [Set.indicator_of_mem]
        exact ⟨hx, rfl⟩
      · exact fun q _ hq => Set.indicator_of_notMem (fun h => hq h.2.symm) _
      · exact fun h => absurd (Finset.mem_univ _) h
    · rw [if_neg hx]
      exact (Finset.sum_eq_zero fun q _ => Set.indicator_of_notMem (fun h => hx h.1) _).symm
  have hi : ∀ q, Integrable ({x | x ∈ I.Kset ∧ ρ.toFun x = q}.indicator (fun _ => F q)) μf := fun q =>
    (integrable_indicator_iff (hm q).1).2 (integrableOn_const ((hm q).2 ▸ hfin))
  rw [e]
  refine ⟨integrable_finset_sum _ fun q _ => hi q, ?_⟩
  rw [integral_finset_sum _ fun q _ => hi q, Finset.mul_sum]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_indicator_const _ (hm q).1, Measure.real, (hm q).2, Complex.real_smul]

theorem integrable_lift [Finite Q] (μf : Measure I.Gf) [μf.IsHaarMeasure] (hg : 1 ≤ g) (a : MonoidAlgebra ℂ Q) :
    Integrable (ρ.lift μf a) μf := by
  letI := Fintype.ofFinite Q
  exact (integral_inflate ρ μf hg fun q => a.coeff q / ((μf (I.Kg g)).toReal : ℂ)).1

theorem lift_biinv (μf : Measure I.Gf) (a : MonoidAlgebra ℂ Q) (x : I.Gf) (k : I.Gf) (hk : k ∈ I.Kg g)
    (k' : I.Gf) (hk' : k' ∈ I.Kg g) : ρ.lift μf a (k * x * k') = ρ.lift μf a x := by
  by_cases hx : x ∈ I.Kset
  · have h1 : k * x ∈ I.Kset := (Ksub I).mul_mem hk.1 hx
    rw [ρ.lift_of_mem μf a hx, ρ.lift_of_mem μf a ((Ksub I).mul_mem h1 hk'.1), ρ.map_mul _ h1 _ hk'.1,
      ρ.map_mul _ hk.1 _ hx, (ρ.ker _ hk.1).2 hk, (ρ.ker _ hk'.1).2 hk', one_mul, mul_one]
  · rw [ρ.lift_of_notMem μf a hx, ρ.lift_of_notMem μf a fun h => hx
      (((Ksub I).mul_mem_cancel_left hk.1).1 (((Ksub I).mul_mem_cancel_right hk'.1).1 h))]

end Infl

end GlobalTheory.Mem.RowsBundle
