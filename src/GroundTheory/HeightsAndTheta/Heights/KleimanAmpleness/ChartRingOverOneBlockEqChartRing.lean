import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.IsGraphGenTwistBundleZero

set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH (chartRingOver secOver)

noncomputable section

variable {S : Type} [CommRing S] {Ω : Type} [Field Ω] [Algebra S Ω]

section Frac

theorem coe_ne_zero_of_not_mem {A : Subalgebra S Ω} {p : Ideal A} {b : A} (hb : b ∉ p) : (b : Ω) ≠ 0 := by
  intro h
  apply hb
  have : b = 0 := Subtype.ext h
  rw [this]
  exact p.zero_mem

theorem one_not_mem_of_prime {A : Subalgebra S Ω} {p : Ideal A} (hp : p.IsPrime) : (1 : A) ∉ p :=
  fun h => hp.ne_top ((Ideal.eq_top_iff_one _).mpr h)

def fracSub (A : Subalgebra S Ω) (p : Ideal A) [hp : p.IsPrime] : Subalgebra S Ω where
  carrier := {u | ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b}
  mul_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_mul_div_comm]
  add_mem' := by
    rintro _ _ ⟨a, b, hb, rfl⟩ ⟨a', b', hb', rfl⟩
    refine ⟨a * b' + b * a', b * b', fun h => (hp.mem_or_mem h).elim hb hb', ?_⟩
    push_cast
    rw [div_add_div _ _ (coe_ne_zero_of_not_mem hb) (coe_ne_zero_of_not_mem hb')]
  algebraMap_mem' r := ⟨algebraMap S A r, 1, one_not_mem_of_prime hp, by simp⟩

theorem mem_locIn {A : Subalgebra S Ω} {p : Ideal A} [p.IsPrime] {u : Ω} :
    u ∈ IndefiniteRowSideFullHecke.Kleiman2.locIn A p ↔ ∃ a b : A, b ∉ p ∧ u = (a : Ω) / b := by
  constructor
  · intro h
    exact (Subring.closure_le (t := (fracSub A p).toSubring)).mpr (fun v hv => hv) h
  · intro h
    exact Subring.subset_closure h

theorem span_subset_span {A B : Subalgebra S Ω} (hAB : A ≤ B) (s : Set Ω) :
    (Submodule.span A s : Set Ω) ⊆ Submodule.span B s := by
  intro z (hz : z ∈ Submodule.span A s)
  induction hz using Submodule.span_induction with
  | mem z hz => exact Submodule.subset_span hz
  | zero => exact Submodule.zero_mem _
  | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
  | smul a z _ hz =>
    have e : a • z = (⟨a, hAB a.2⟩ : B) • z := by
      rw [Subalgebra.smul_def, Subalgebra.smul_def]
    rw [SetLike.mem_coe, e]
    exact Submodule.smul_mem _ _ hz

theorem chartRingOver_oneBlock_eq_chartRing {N : ℕ} (x : Fin (N + 1) → Ω) (c : Unit → Fin (N + 1)) (h : x (c ()) ≠ 0) :
    chartRingOver S (IndefiniteRowSideFullHecke.Kleiman2.oneBlock x) c = Kleiman.chartRing S x (Kleiman.singleChart h) := by
  rw [← TranslateEq.chartRing.equiv S x h]
  unfold chartRingOver ReciprocityTheory.ChartRestriction.G.Geo.chartRing
  congr 1
  ext z
  constructor
  · rintro ⟨⟨⟨⟩, a⟩, rfl⟩
    exact ⟨a, rfl⟩
  · rintro ⟨a, rfl⟩
    exact ⟨⟨(), a⟩, rfl⟩

end Frac

end

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
