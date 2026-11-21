import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IwasawaBlockTriangular
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiagPartMulDiagPart
open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.RootEx.Unram
open GlobalTheory.StepData

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ}

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_not_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : ¬ _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = _root_.GlobalTheory.RootEx.basePt c x₀ r s := by
  simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply, dif_neg hf, add_zero]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem affPt_apply_of_free {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) {r : n ⊕ Fin c} {s : n' ⊕ Fin (c + 1)}
    (hf : _root_.GlobalTheory.RootEx.Free p (r, s)) :
    _root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e r s = e ⟨(r, s), hf⟩ := by
  simp only [_root_.GlobalTheory.RootEx.affPt, _root_.GlobalTheory.RootEx.basePt, Matrix.add_apply,
    Matrix.of_apply, dif_pos hf]
  have hf' := hf
  rcases r with i | l <;> rcases s with j | m <;> simp only [_root_.GlobalTheory.RootEx.Free] at hf' <;>
    simp [Matrix.fromBlocks_apply₁₂, Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂] <;>
    omega

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem intM_basePt_of_intM {x₀ : Matrix n n' k}
    (hx : _root_.GlobalTheory.StepData.IntM x₀) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.basePt c x₀) := by
  unfold _root_.GlobalTheory.RootEx.basePt
  refine _root_.GlobalTheory.StepData.intM_fromBlocks.mpr
    ⟨hx, _root_.GlobalTheory.StepData.intM_zero, _root_.GlobalTheory.StepData.intM_zero, fun l i => ?_⟩
  simp only [Matrix.of_apply]
  split_ifs
  exacts [one_mem _, zero_mem _]

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
omit [TopologicalSpace k] [IsNonarchimedeanLocalField k] [Fintype n] [DecidableEq n] [Fintype n']
  [DecidableEq n'] in
theorem _root_.GlobalTheory.RootEx.Unram.intM_affPt {p : ℕ} (x₀ : Matrix n n' k) (e) :
    _root_.GlobalTheory.StepData.IntM (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ↔
      _root_.GlobalTheory.StepData.IntM x₀ ∧ ∀ rs, e rs ∈ 𝒪[k] := by
  constructor
  · intro h
    refine ⟨fun i j => ?_, fun rs => ?_⟩
    · have hij := h (Sum.inl i) (Sum.inl j)
      rwa [affPt_apply_of_not_free x₀ e (by simp [_root_.GlobalTheory.RootEx.Free]),
        _root_.GlobalTheory.RootEx.basePt, Matrix.fromBlocks_apply₁₁] at hij
    · obtain ⟨⟨r, s⟩, hf⟩ := rs
      have hrs := h r s
      rwa [affPt_apply_of_free x₀ e hf] at hrs
  · rintro ⟨hx, he⟩ r s
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · rw [affPt_apply_of_free x₀ e hf]
      exact he _
    · rw [affPt_apply_of_not_free x₀ e hf]
      exact intM_basePt_of_intM hx r s

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.psi_eq_one {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k} (hx : x ∈ 𝒪[k]) : ψ x = 1 := by
  have h1 := (hψ x).mpr (by
    rw [Units.val_one, map_one]
    exact (Valuation.mem_integer_iff _ _).mp hx)
  exact h1 x le_rfl

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
theorem _root_.GlobalTheory.RootEx.Unram.mem_of_psi {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {x : k}
    (hx : ∀ t ∈ 𝒪[k], ψ (t * x) = 1) : x ∈ 𝒪[k] := by
  rw [Valuation.mem_integer_iff]
  have hmain := (hψ x).mp ?_
  · simpa using hmain
  intro y hy
  by_cases hx0 : x = 0
  · subst hx0
    have hy0 : y = 0 := by simpa using hy
    simp [hy0]
  · have hv : valuation k (y / x) ≤ 1 := by
      rw [map_div₀]
      exact div_le_one_of_le₀ hy zero_le'
    have hyx := hx (y / x) ((Valuation.mem_integer_iff _ _).mpr hv)
    rwa [div_mul_cancel₀ y hx0] at hyx

variable [MeasurableSpace k] [BorelSpace k]

open ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] {n n' : Type} {c : ℕ} in
private theorem ch_affPt_mem_of_integral {p : ℕ} (x₀ : Matrix n n' k)
    (e : { rs // _root_.GlobalTheory.RootEx.Free p rs } → k) (he : ∀ rs, e rs ∈ 𝒪[k]) :
    _root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt (c := c) p x₀ e) ∈ 𝒪[k] := by
  unfold _root_.GlobalTheory.RootEx.ch
  refine sum_mem fun i _ => ?_
  have hf : _root_.GlobalTheory.RootEx.Free (n := n) (n' := n') p (Sum.inr i, Sum.inr i.succ) := by
    simp [_root_.GlobalTheory.RootEx.Free]
  rw [affPt_apply_of_free x₀ e hf]
  exact he _

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in
open Classical in
theorem _root_.GlobalTheory.RootEx.Unram.opE_of_ite {p : ℕ} {ψ : AddChar k Circle}
    (hψ : _root_.GlobalTheory.SplitWeil.HasConductor ψ 1) {ν : Measure k} (hν : _root_.GlobalTheory.SplitWeil.IsUnitVol ν)
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k) (P : Prop)
    (h : ∀ e, Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) = if P ∧ ∀ rs, e rs ∈ 𝒪[k] then 1 else 0) :
    _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ = if P then 1 else 0 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  haveI := hν.1
  set S : Set ({ rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k) :=
    Set.univ.pi fun _ => (𝒪[k] : Set k) with hS
  have hSm : MeasurableSet S :=
    MeasurableSet.univ_pi fun _ => (_root_.GlobalTheory.SplitWeil.isOpen_int k).measurableSet
  have hint : ∀ e : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k,
      Ψ (_root_.GlobalTheory.RootEx.affPt p x₀ e) *
          ((ψ (-_root_.GlobalTheory.RootEx.ch (_root_.GlobalTheory.RootEx.affPt p x₀ e)) : Circle) : ℂ) =
        if P then S.indicator (fun _ => (1 : ℂ)) e else 0 := by
    intro e
    rw [h e]
    by_cases hP : P
    · by_cases he : ∀ rs, e rs ∈ 𝒪[k]
      · have heS : e ∈ S := fun rs _ => he rs
        rw [if_pos ⟨hP, he⟩, if_pos hP, Set.indicator_of_mem heS,
          _root_.GlobalTheory.RootEx.Unram.psi_eq_one hψ
            (neg_mem (ch_affPt_mem_of_integral x₀ e he))]
        simp
      · have heS : e ∉ S := fun heS => he fun rs => heS rs (Set.mem_univ _)
        rw [if_neg (fun h' => he h'.2), if_pos hP, Set.indicator_of_notMem heS, zero_mul]
    · rw [if_neg (fun h' => hP h'.1), if_neg hP, zero_mul]
  unfold _root_.GlobalTheory.RootEx.opE
  simp_rw [hint]
  split_ifs with hP
  · rw [integral_indicator_const _ hSm, Measure.real_def, hS, Measure.pi_pi]
    simp [hν.2]
  · simp

open MeasureTheory ValuativeRel Matrix in
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] in
variable {n n' : Type} [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] {c : ℕ} in
variable [MeasurableSpace k] [BorelSpace k] in
omit [DecidableEq n] [DecidableEq n'] in

theorem _root_.GlobalTheory.RootEx.Unram.psi_ch_eq_one {p : ℕ} (ψ : AddChar k Circle)
    (ν : Measure k) [ν.IsAddHaarMeasure]
    (Ψ : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k → ℂ) (x₀ : Matrix n n' k)
    (h : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ ≠ 0)
    (D : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)
    (hD : ∀ r s, ¬ _root_.GlobalTheory.RootEx.Free p (r, s) → D r s = 0)
    (hΨ : ∀ x, Ψ (x + D) = Ψ x) : ψ (-_root_.GlobalTheory.RootEx.ch D) = 1 := by
  haveI := _root_.GlobalTheory.SplitWeil.secondCountable k
  set d : { rs // _root_.GlobalTheory.RootEx.Free (n := n) (c := c) (n' := n') p rs } → k :=
    fun rs => D rs.1.1 rs.1.2 with hd
  have haff : ∀ e, _root_.GlobalTheory.RootEx.affPt p x₀ (e + d) = _root_.GlobalTheory.RootEx.affPt p x₀ e + D := by
    intro e
    ext r s
    simp only [_root_.GlobalTheory.RootEx.affPt, Matrix.add_apply, Matrix.of_apply]
    by_cases hf : _root_.GlobalTheory.RootEx.Free p (r, s)
    · simp only [dif_pos hf, Pi.add_apply, hd]
      ring
    · simp only [dif_neg hf, hD r s hf, add_zero]
  have hch : ∀ A B : Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k,
      _root_.GlobalTheory.RootEx.ch (A + B) =
        _root_.GlobalTheory.RootEx.ch A + _root_.GlobalTheory.RootEx.ch B := by
    intro A B
    simp [_root_.GlobalTheory.RootEx.ch, Finset.sum_add_distrib]
  have key : _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ =
      ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) * _root_.GlobalTheory.RootEx.opE ψ ν p Ψ x₀ := by
    unfold _root_.GlobalTheory.RootEx.opE
    rw [← integral_const_mul, ← integral_add_right_eq_self _ d]
    congr 1
    ext e
    rw [haff, hΨ, hch, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul]
    ring
  have h1 : ((ψ (-_root_.GlobalTheory.RootEx.ch D) : Circle) : ℂ) = 1 :=
    mul_right_cancel₀ h (key.symm.trans (one_mul _).symm)
  exact Circle.ext (h1.trans Circle.coe_one.symm)

end GlobalTheory.RootEx.Unram
