import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.CmLatticeCommutatorPairingPowEqOneOfGoodLift
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.LatticeInvariantsPeriodPairDictionary
open Cardinal
namespace GlobalTheory.MomOne.Inh

theorem mk_le {A X : Type} [MetricSpace X] (f : A → X) (hf : DenseRange f) (hA : #A ≤ 𝔠) :
    #X ≤ 𝔠 := by
  have h : ∀ x : X, ∃ s : ℕ → A, Filter.Tendsto (fun n => f (s n)) Filter.atTop (nhds x) := fun x => by
    obtain ⟨u, hu, hx⟩ := mem_closure_iff_seq_limit.1 (hf x)
    choose s hs using hu
    exact ⟨s, by simpa only [hs] using hx⟩
  choose s hs using h
  have hinj : Function.Injective s := fun x y hxy =>
    tendsto_nhds_unique (hs x) (by rw [hxy]; exact hs y)
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  rw [← Cardinal.power_def, Cardinal.mk_nat]
  exact (Cardinal.power_le_power_right hA).trans_eq Cardinal.continuum_power_aleph0

theorem nonempty_iso (p : ℕ) [Fact p.Prime] : Nonempty (ℂ ≃+* ℂ_[p]) := by
  have h1 : #ℚ_[p] ≤ 𝔠 := mk_le _ (Padic.denseRange_ratCast p)
    (Cardinal.mk_le_aleph0.trans Cardinal.aleph0_le_continuum)
  have h2 : #(PadicAlgCl p) ≤ 𝔠 :=
    (Algebra.IsAlgebraic.cardinalMk_le_max ℚ_[p] (PadicAlgCl p)).trans (max_le h1 Cardinal.aleph0_le_continuum)
  have h3 : #(ℂ_[p]) ≤ 𝔠 := mk_le (X := PadicComplex p) _
    (UniformSpace.Completion.denseRange_coe (α := PadicAlgCl p)) h2
  have h4 : 𝔠 ≤ #(ℂ_[p]) := continuum_le_cardinal_of_nontriviallyNormedField _
  refine IsAlgClosed.ringEquiv_of_equiv_of_charZero (by rw [Cardinal.mk_complex]; exact Cardinal.aleph0_lt_continuum) ?_
  exact Cardinal.eq.1 (by rw [Cardinal.mk_complex]; exact le_antisymm h4 h3)

end GlobalTheory.MomOne.Inh
