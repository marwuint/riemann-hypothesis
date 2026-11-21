import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.Definitions.Foundations.SecondCountableAndT2LocalField
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsOpenSetOfLeRank
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocallyConstantExtensionByZero

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL Matrix Topology

namespace GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences

theorem comp_mem_SB_of_isInducing {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] {i : Y → X}
    (hi : IsInducing i) (Φ : SB X) {C : Set X} (hC : IsClosed C) (hiC : ∀ y, i y ∈ C)
    (hs : ∀ x ∈ C, Φ.1 x ≠ 0 → x ∈ Set.range i) : (fun y => Φ.1 (i y)) ∈ SB Y := by
  refine ⟨Φ.2.1.comp_continuous hi.continuous, ?_⟩
  have h0 : IsClosed (Function.support Φ.1) := (Φ.2.1.isOpen_fiber 0).isClosed_compl
  have h1 : IsCompact (Function.support Φ.1) := Φ.2.2.of_isClosed_subset h0 subset_closure
  have h2 : IsCompact (i ⁻¹' (Function.support Φ.1 ∩ C)) :=
    hi.isCompact_preimage' (h1.inter_right hC) fun x hx => hs x hx.2 hx.1
  refine HasCompactSupport.intro' h2 ((h0.inter hC).preimage hi.continuous) fun y hy => ?_
  by_contra h
  exact hy ⟨h, hiC y⟩

section

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

omit [DecidableEq a] [DecidableEq b] in

theorem isOpen_le_rank (κ : ℕ) : IsOpen {x : Matrix b a k | κ ≤ x.rank} := by
  obtain ⟨_, _⟩ := SplitWeil.Model.secondCountable_and_t2_local_field (k := k)
  exact GlobalTheory.isOpen_setOf_le_rank k b a κ

omit [DecidableEq a] [DecidableEq b] in

theorem isClosed_rank_lt (κ : ℕ) : IsClosed {x : Matrix b a k | x.rank < κ} := by
  have := (isOpen_le_rank (k := k) (a := a) (b := b) κ).isClosed_compl
  simpa only [Set.compl_ofPred, not_le] using this

def resFilt (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m) :
    (filt a b μ (Set.Iio n) κ).toRepresentation.IntertwiningMap (omegaOn a b μ s) where
  toFun Φ := ⟨fun x => Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩,
    comp_mem_SB_of_isInducing
      (i := fun x : RankIn k a b s => (⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ : RankIn k a b (Set.Iio n)))
      (IsInducing.subtypeVal.of_comp_iff.1 IsInducing.subtypeVal) Φ.1
      ((isClosed_rank_lt m).preimage continuous_subtype_val) (fun y => ((hs _).1 y.2).2)
      fun x hx h0 => ⟨⟨x.1, (hs _).2 ⟨not_lt.1 fun h => h0 (Φ.2 x h), hx⟩⟩, rfl⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  isIntertwining' _ := rfl

theorem resFilt_apply (μ : kˣ →* ℂˣ) {s : Set ℕ} {κ m n : ℕ} (hmn : m ≤ n) (hs : ∀ r, r ∈ s ↔ κ ≤ r ∧ r < m)
    (Φ : (filt a b μ (Set.Iio n) κ).toSubmodule) (x : RankIn k a b s) :
    (resFilt μ hmn hs Φ).1 x = Φ.1.1 ⟨x.1, ((hs _).1 x.2).2.trans_le hmn⟩ := rfl

end

end GlobalTheory.IndefiniteRowSideFullHecke.OpenClosedSequences
