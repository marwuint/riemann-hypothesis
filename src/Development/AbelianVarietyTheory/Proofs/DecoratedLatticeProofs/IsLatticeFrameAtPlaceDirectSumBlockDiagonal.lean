module

public import Development.AbelianVarietyTheory.Definitions.Foundations.NotIsSplitOfIsInertAt
public import Development.AbelianVarietyTheory.Definitions.Foundations.MemSiegelOfIffRightAct
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.Definitions.Divisors.EqOfHasValueAtInfinite

@[expose] public section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.PRep
open Formalism.UG (IsUnifV qV IsUnramInv GU KU IsInertAt Hecke ordL)
open Formalism.MainNotions.SchurIrreducible (IsSplit)
open GlobalTheory.LGrp (bcParam)
open GlobalTheory.LFun (toCompl locMat locChar IsSplitChart IsInertChart IsFrameAt KGL IsSatVecGL IsSatVecU eulerFac UnrAt LvTw dv Fam)

namespace GlobalTheory.LFun

theorem latAt_sumLat_self {E : Type} [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) {n : ℕ}
    (L : Submodule (𝓞 E) (Fin n → E)) :
    latAt w (sumLat finSumFinEquiv L L) = sumLat finSumFinEquiv (latAt w L) (latAt w L) := by
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  have hadd : ∀ {X : Type} [AddCommGroup X] (x y : Fin n → X),
      pairVec e (x + y) 0 = pairVec e x 0 + pairVec e y 0 ∧
        pairVec e 0 (x + y) = pairVec e 0 x + pairVec e 0 y := by
    intro X _ x y
    constructor <;> funext j <;> obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsm : ∀ (c : Formalism.UG.Ov E w) (x : Fin n → w.adicCompletion E),
      pairVec e (c • x) 0 = c • pairVec e x 0 ∧ pairVec e 0 (c • x) = c • pairVec e 0 x := by
    intro c x
    constructor <;> funext j <;> obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  have hsplit : ∀ (x y : Fin n → w.adicCompletion E), pairVec e x y = pairVec e x 0 + pairVec e 0 y := by
    intro x y; funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
  set φ : (Fin n → E) → (Fin n → w.adicCompletion E) := fun x i => algebraMap E (w.adicCompletion E) (x i)
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, mem_sumLat] at hx ⊢
    exact ⟨Submodule.subset_span ⟨_, hx.1, rfl⟩, Submodule.subset_span ⟨_, hx.2, rfl⟩⟩
  · intro z hz'
    rw [← pairVec_eta e z, pairVec_mem_sumLat] at hz'
    rw [← pairVec_eta e z, hsplit]
    refine Submodule.add_mem _ ?_ ?_
    · have hu' := hz'.1
      generalize (fun i => z (e (.inl i))) = u at hu' ⊢
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e y 0, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨hy, L.zero_mem⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => simp [pairVec]
      | add x y _ _ hx hy => rw [(hadd _ _).1]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [(hsm _ _).1]; exact Submodule.smul_mem _ c hx
    · have hu' := hz'.2
      generalize (fun i => z (e (.inr i))) = u at hu' ⊢
      induction hu' using Submodule.span_induction with
      | mem x hx =>
        obtain ⟨y, hy, rfl⟩ := hx
        refine Submodule.subset_span ⟨pairVec e 0 y, ?_, ?_⟩
        · rw [SetLike.mem_coe, pairVec_mem_sumLat]; exact ⟨L.zero_mem, hy⟩
        · funext j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp
      | zero => simp [pairVec]
      | add x y _ _ hx hy => rw [(hadd _ _).2]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [(hsm _ _).2]; exact Submodule.smul_mem _ c hx

theorem isFrameAt_sumLat_blkGL : ∀ (E : Type) [Field E] [NumberField E] (w : HeightOneSpectrum (𝓞 E)) (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (a : GL (Fin n) (w.adicCompletion E)), IsFrameAt w L a → IsFrameAt w (sumLat finSumFinEquiv L L) (blkGL finSumFinEquiv (a, a)) := by
  intro E _ _ w n L a ha y
  set e : Fin n ⊕ Fin n ≃ Fin (n + n) := finSumFinEquiv
  rw [latAt_sumLat_self, ← pairVec_eta e y, val_blkGL, blkMat_mulVec, pairVec_mem_sumLat,
    ← ha, ← ha]
  constructor
  · intro h; exact ⟨fun i => by simpa using h (e (.inl i)), fun i => by simpa using h (e (.inr i))⟩
  · rintro ⟨h1, h2⟩ j; obtain ⟨i | i, rfl⟩ := e.surjective j <;> simp [h1, h2]

end GlobalTheory.LFun
