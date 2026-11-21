import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ValueDoubleExact
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HomLatticeCompletionSelfAnnihilatorAtPlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMaps
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymplOHEqZeroOfHO
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.FinPl
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.FinPl.FlatFix

variable {D : D7}

theorem two_ne_zero_at (w : Pl D) : (2 : Fv D.host.F w) ≠ 0 := by
  rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]
  exact (map_ne_zero_iff _ (algebraMap D.host.F (Fv D.host.F w)).injective).2 two_ne_zero

theorem two_inv_int (w : Pl D) (hw : (2 : 𝓞 D.host.F) ∉ w.asIdeal) :
    (2⁻¹ : Fv D.host.F w) ∈ w.adicCompletionIntegers D.host.F := by
  have h3 : HeightOneSpectrum.valuation D.host.F w (2 : D.host.F) = 1 := by
    have := HeightOneSpectrum.valuation_of_algebraMap (K := D.host.F) w (2 : 𝓞 D.host.F)
    rw [HeightOneSpectrum.intValuation_eq_one_iff.2 hw] at this
    rw [← this]
    congr 1
  have h2 : ((2 : D.host.F) : Fv D.host.F w) = 2 := by
    rw [← map_ofNat (algebraMap D.host.F (Fv D.host.F w)) 2]; rfl
  rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, ← h2,
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation', h3, inv_one]

theorem finite_two (P : Pl D → Prop) : {v : Pl D | P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal}.Finite := by
  have h0 : Ideal.span {(2 : 𝓞 D.host.F)} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact two_ne_zero
  refine (Ideal.finite_factors h0).subset fun v hv => ?_
  exact (Ideal.dvd_span_singleton).2 hv.2

open Classical in

def halfOff (P : Pl D → Prop) : Af D.host.F :=
  RestrictedProduct.mk (fun w => if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0)
    (Filter.Eventually.of_forall fun w => by
      split_ifs with h
      · exact two_inv_int w h.2
      · exact zero_mem _)

open Classical in
theorem evalV_halfOff (P : Pl D → Prop) (w : Pl D) :
    evalV D.host.F w (halfOff P) = if P w ∧ (2 : 𝓞 D.host.F) ∉ w.asIdeal then (2⁻¹ : Fv D.host.F w) else 0 := rfl

theorem halfOff_int (P : Pl D → Prop) : halfOff P ∈ intAf D.host.F := by
  classical
  intro w
  rw [evalV_halfOff]
  split_ifs with h
  · exact two_inv_int w h.2
  · exact zero_mem _

theorem pair_add (a b : Af D.host.F) : pairA D.host.F 0 (a + b) = pairA D.host.F 0 a + pairA D.host.F 0 b :=
  Prod.ext (add_zero (0 : Ainf D.host.F)).symm rfl

theorem sum_pair {ι : Type} (s : Finset ι) (α : ι → Af D.host.F) :
    ∑ i ∈ s, pairA D.host.F 0 (α i) = pairA D.host.F 0 (∑ i ∈ s, α i) := by
  classical
  induction s using Finset.induction_on with
  | empty => exact Prod.ext rfl rfl
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, ih, pair_add]

theorem indicatorIdempotent_eq_add_sum (P : Pl D → Prop) (Qs : Finset (Pl D)) (hQ : ∀ v, v ∈ Qs ↔ P v ∧ (2 : 𝓞 D.host.F) ∈ v.asIdeal)
    (ε : Pl D → AF D.host.F) (hε : ∀ v ∈ Qs, IsPlaceIdem D v (ε v)) :
    GlobalTheory.SelfDualAt.cP P = pairA D.host.F 0 (halfOff P + halfOff P) + ∑ v ∈ Qs, ε v := by
  classical
  choose! α hα h1 h0 using hε
  rw [Finset.sum_congr rfl hα, sum_pair, ← pair_add]
  unfold GlobalTheory.SelfDualAt.cP
  congr 1
  refine FiniteAdeleRing.ext (R := 𝓞 D.host.F) D.host.F fun w => ?_
  change evalV D.host.F w (GlobalTheory.SelfDualAt.indP P) = evalV D.host.F w (halfOff P + halfOff P + ∑ i ∈ Qs, α i)
  rw [map_add, map_add, map_sum, GlobalTheory.SelfDualAt.evalV_indP, evalV_halfOff]
  by_cases hw : w ∈ Qs
  · obtain ⟨hP, h2⟩ := (hQ w).1 hw
    rw [Finset.sum_eq_single_of_mem w hw (fun v hv hvw => h0 v hv w (Ne.symm hvw)), h1 w hw, if_pos hP,
      if_neg (fun h => h.2 h2), zero_add, zero_add]
  · rw [Finset.sum_eq_zero (fun v hv => h0 v hv w (fun h => hw (h ▸ hv))), add_zero]
    by_cases hP : P w
    · have h2 : (2 : 𝓞 D.host.F) ∉ w.asIdeal := fun h2 => hw ((hQ w).2 ⟨hP, h2⟩)
      rw [if_pos hP, if_pos ⟨hP, h2⟩, ← two_mul, mul_inv_cancel₀ (two_ne_zero_at w)]
    · rw [if_neg hP, if_neg (fun h => hP h.1), add_zero]

theorem int_alg_pair {β : Af D.host.F} (hβ : β ∈ intAf D.host.F) :
    finPart D (algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β)) ∈ intAE D := by
  have e : algebraMap (AF D.host.F) (AE D) (pairA D.host.F 0 β) = pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E) := rfl
  have e2 : finPart D (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) =
      β ⊗ₜ[D.host.F] ((1 : 𝓞 D.host.E) : D.host.E) := by
    show Algebra.TensorProduct.map (sndA D.host.F) (AlgHom.id _ _) (pairA D.host.F 0 β ⊗ₜ[D.host.F] (1 : D.host.E)) = _
    rw [Algebra.TensorProduct.map_tmul]; rfl
  rw [e, e2]
  exact AddSubgroup.subset_closure ⟨β, hβ, 1, rfl⟩

end GlobalTheory.FinPl.FlatFix

end
