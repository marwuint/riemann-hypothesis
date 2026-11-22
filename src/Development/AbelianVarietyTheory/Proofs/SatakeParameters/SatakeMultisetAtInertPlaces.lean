import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.TendstoOneOfSummable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GoodLabelsRankPartParameterCuspidal
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TieAutAndSplit
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularDefinite
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace GlobalTheory.UbcString

theorem not_isSplitPl_of_inert {R : Ranks} (H : Host R) (w : HeightOneSpectrum (𝓞 H.E))
    (hw : Formalism.UG.IsInertAt H.F H.E (w.under (𝓞 H.F)) w) : ¬ IsSplitPl H w := by
  rintro ⟨x, hx, hy⟩
  let c : 𝓞 H.E ≃+* 𝓞 H.E := RingOfIntegers.mapRingEquiv (H.conj : H.E ≃+* H.E)
  have hc : ∀ z : 𝓞 H.E, ((c z : 𝓞 H.E) : H.E) = H.conj (z : H.E) := fun z => rfl
  have hfix : ∀ a : 𝓞 H.F, c (algebraMap (𝓞 H.F) (𝓞 H.E) a) = algebraMap (𝓞 H.F) (𝓞 H.E) a := by
    intro a
    apply RingOfIntegers.ext
    rw [hc]
    have e : ((algebraMap (𝓞 H.F) (𝓞 H.E) a : 𝓞 H.E) : H.E) = ((a : H.F) : H.E) := rfl
    rw [e]
    exact (H.conjE_mem_hostF_iff _).1 (a : H.F).2
  have hle : w.asIdeal ≤ w.asIdeal.comap (c : 𝓞 H.E →+* 𝓞 H.E) := by
    unfold Formalism.UG.IsInertAt at hw
    rw [← hw, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap, Ideal.mem_comap]
    change c (algebraMap (𝓞 H.F) (𝓞 H.E) a) ∈ _
    rw [hfix]
    exact Ideal.mem_map_of_mem _ ha
  exact hy (c x) (hc x) (hle hx)

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R} {N : NData R H what₂} (A : NAut N)

theorem unr_of_foldr {w : PlE H} (a : A.LP w) (f : ℝ → ℝ) (L : List ℝ) (k : ℝ) (hk : k ∈ L)
    (h : A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w))) : A.unr a := by
  induction L with
  | nil => simp at hk
  | cons j L ih =>
    rw [List.foldr_cons, A.unr_sum] at h
    rcases List.mem_cons.1 hk with rfl | hk
    · exact (A.unr_tw a _).1 h.1
    · exact ih hk h.2

theorem frobEig_foldr {w : PlE H} (a : A.LP w) (ha : A.unr a) (f : ℝ → ℝ) (L : List ℝ) :
    A.unr (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) ∧
    A.frobEig (L.foldr (fun k acc => A.lpSum (A.lpTw a (f k)) acc) (A.lpZero w)) =
      (L.map fun k => (A.frobEig a).map (· * ((normV w : ℕ) : ℂ) ^ ((f k : ℝ) : ℂ))).sum := by
  induction L with
  | nil => exact ⟨A.lpZero_unr w, A.frobEig_zero w⟩
  | cons k L ih =>
    have hk := (A.unr_tw a (f k)).2 ha
    refine ⟨(A.unr_sum _ _).2 ⟨hk, ih.1⟩, ?_⟩
    simp only [List.foldr_cons, List.map_cons, List.sum_cons]
    rw [A.frobEig_sum _ _ hk ih.1, A.frobEig_tw a _ ha, ih.2]

theorem sum_singletons {ι : Type} (g : ι → ℂ) (L : List ι) :
    (L.map fun k => ({g k} : Multiset ℂ)).sum = ((L.map g : List ℂ) : Multiset ℂ) := by
  induction L with
  | nil => simp
  | cons k L ih => simp [ih]

end GlobalTheory.UbcString

