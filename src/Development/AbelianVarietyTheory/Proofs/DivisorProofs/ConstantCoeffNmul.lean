module

public import Development.AbelianVarietyTheory.Definitions.Divisors.EqZeroOfForallPowDvd
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.EpsilonPairingZeta
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius

@[expose] public section

open MvPowerSeries GlobalTheory GlobalTheory.Katz GlobalTheory.QLog GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.QLogDefect

variable {B Q : Type} [CommRing B] [CommRing Q] [Algebra B Q]

theorem in_zero {σ : Type} (N : Ideal B) : In N (0 : MvPowerSeries σ Q) :=
  fun α => ⟨0, N.zero_mem, by simp⟩

theorem in_sub {σ : Type} {N : Ideal B} {f g : MvPowerSeries σ Q} (hf : In N f) (hg : In N g) :
    In N (f - g) := fun α => by
  obtain ⟨a, ha, hfa⟩ := hf α
  obtain ⟨b, hb, hgb⟩ := hg α
  exact ⟨a - b, N.sub_mem ha hb, by rw [map_sub, hfa, hgb, map_sub]⟩

theorem in_subst {σ τ : Type} [Finite σ] {N : Ideal B} {g : MvPowerSeries σ Q}
    (u : σ → MvPowerSeries τ B) (hu : ∀ i, constantCoeff (u i) = 0) (hg : In N g) :
    In N (subst (up Q u) g) := by
  choose c hcN hc using hg
  set G : MvPowerSeries σ B := fun α => c α with hG
  have hgG : g = map (algebraMap B Q) G := by
    ext α; rw [coeff_map, hc α]; rfl
  have hsu : HasSubst u := hasSubst_of_constantCoeff_zero hu
  have key : subst (up Q u) g = map (algebraMap B Q) (subst u G) := by
    rw [map_subst hsu, hgG]; rfl
  intro e
  refine ⟨coeff e (subst u G), ?_, by rw [key, coeff_map]⟩
  rw [coeff_subst hsu]
  refine finsum_induction (fun x => x ∈ N) N.zero_mem (fun x y hx hy => N.add_mem hx hy) ?_
  intro d
  rw [smul_eq_mul]
  exact N.mul_mem_right _ (hcN d)

variable {d : ℕ}

theorem nmul_succ {R : Type} [CommRing R] (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R) (n : ℕ) :
    nmul μ (n + 1) = op μ (nmul μ n) fun i => X i := by
  unfold nmul; rw [Function.iterate_succ_apply']

theorem constantCoeff_nmul {R : Type} [CommRing R] {μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) R}
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (i : Fin d) : constantCoeff (nmul μ n i) = 0 := by
  induction n generalizing i with
  | zero => simp [nmul]
  | succ n ih =>
    rw [nmul_succ]
    have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) R)) j) = 0 := by
      rintro (j | j)
      · exact ih j
      · simp
    exact constantCoeff_subst_eq_zero (hasSubst_of_constantCoeff_zero h0) h0 (hμ i)

theorem up_nmul_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) :
    up Q (nmul μ (n + 1)) = op (up Q μ) (up Q (nmul μ n)) fun i => X i := by
  funext i
  have h0 : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
    rintro (j | j)
    · exact constantCoeff_nmul hμ n j
    · simp
  rw [nmul_succ]
  simp only [up, op, at2]
  rw [map_subst (hasSubst_of_constantCoeff_zero h0)]
  congr 1
  funext j
  rcases j with j | j
  · rfl
  · simp

theorem defect_succ (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B)
    (hμ : ∀ i, constantCoeff (μ i) = 0) (n : ℕ) (f : MvPowerSeries (Fin d) Q) :
    defect μ (n + 1) f = defect μ n f -
      subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (cob1 (up Q μ) f) := by
  have hU : ∀ j, constantCoeff (up Q (nmul μ n) j) = 0 := by
    intro j
    simp only [up]
    rw [constantCoeff_map, constantCoeff_nmul hμ n j, map_zero]
  have hE : ∀ j, constantCoeff (Sum.elim (up Q (nmul μ n)) (fun i => (X i : MvPowerSeries (Fin d) Q)) j) = 0 := by
    rintro (j | j) <;> simp [hU]
  have hM : ∀ j, constantCoeff (up Q μ j) = 0 := by
    intro j
    simp only [up]
    rw [constantCoeff_map, hμ j, map_zero]
  have hsE := hasSubst_of_constantCoeff_zero hE
  have hsM := hasSubst_of_constantCoeff_zero hM
  have hsL : HasSubst (fun i => (X (Sum.inl i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have hsR : HasSubst (fun i => (X (Sum.inr i) : MvPowerSeries (Fin d ⊕ Fin d) Q)) :=
    hasSubst_of_constantCoeff_zero fun _ => constantCoeff_X _
  have e1 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (subst (up Q μ) f)
      = subst (up Q (nmul μ (n + 1))) f := by
    rw [subst_comp_subst_apply hsM hsE, up_nmul_succ μ hμ n]; rfl
  have e2 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inL f)
      = subst (up Q (nmul μ n)) f := by
    unfold inL
    rw [subst_comp_subst_apply hsL hsE]
    simp only [subst_X hsE, Sum.elim_inl]
  have e3 : subst (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) (inR f) = f := by
    unfold inR
    rw [subst_comp_subst_apply hsR hsE]
    simp only [subst_X hsE, Sum.elim_inr, subst_self, id_eq]
  unfold cob1
  rw [← coe_substAlgHom hsE, map_sub, map_sub, coe_substAlgHom, e1, e2, e3]
  unfold defect
  push_cast
  rw [add_smul, one_smul]
  abel

theorem main : ∀ (p : ℕ) [Fact p.Prime] (B O Q : Type) [CommRing B] [CommRing Q] [CommRing O] [Algebra B Q] (θ : B →+* O), IsFrame p Q θ → ∀ (d : ℕ) (μ : Fin d → MvPowerSeries (Fin d ⊕ Fin d) B), IsLift θ μ → ∀ (N : Ideal B) (f : MvPowerSeries (Fin d) Q), QL μ N f → ∀ n, In N (defect μ n f) ∧ ∀ i, constantCoeff (nmul μ n i) = 0 := by
  intro p _ B O Q _ _ _ _ θ _ d μ hμ N f hf n
  refine ⟨?_, constantCoeff_nmul hμ.const n⟩
  induction n with
  | zero =>
    have h0 : up Q (nmul μ 0) = 0 := by funext i; simp [up, nmul]
    simp only [defect, h0, Nat.cast_zero, zero_smul, zero_sub]
    rw [subst_zero_of_constantCoeff_zero hf.1, neg_zero]
    exact in_zero N
  | succ n ih =>
    rw [defect_succ μ hμ.const n f]
    refine in_sub ih ?_
    have hv : ∀ j, constantCoeff (Sum.elim (nmul μ n) (fun i => (X i : MvPowerSeries (Fin d) B)) j) = 0 := by
      rintro (j | j)
      · exact constantCoeff_nmul hμ.const n j
      · simp
    have : (Sum.elim (up Q (nmul μ n)) fun i => (X i : MvPowerSeries (Fin d) Q)) =
        up Q (Sum.elim (nmul μ n) fun i => (X i : MvPowerSeries (Fin d) B)) := by
      funext j; rcases j with j | j
      · rfl
      · simp [up]
    rw [this]
    exact in_subst _ hv hf.2.2

end GlobalTheory.QLogDefect
