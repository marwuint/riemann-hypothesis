module

import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionEqAndWeilIsOfIsHolTo
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.HolFamilyOfIsPullback
public import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Bernstein
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
import Mathlib.Tactic.Basify
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
import Std.Tactic.BVDecide.Normalize.Prop

@[expose] public section

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.HolFibre

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem isHolTo_comp {W : Set E} {X Y : Scheme.{0}} {c : E → (Sp ℂ ⟶ X)} (hc : IsHolTo W c) (ψ : X ⟶ Y) :
    IsHolTo W (fun w => c w ≫ ψ) := by
  intro U f
  have := hc (ψ ⁻¹ᵁ U) ((ψ.app U).hom f)
  simpa only [valAt'_comp, ← top_le_preimage_comp] using this

theorem isHolTo_const {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (x : Sp ℂ ⟶ X) :
    IsHolTo W (fun _ => x) := by
  intro U f
  refine ⟨?_, differentiableOn_const _⟩
  by_cases h : ⊤ ≤ x ⁻¹ᵁ U
  · simp only [h, and_true]
    exact hW
  · simp only [h, and_false, Set.setOf_false, isOpen_empty]

theorem isHolTo_of_isPullback {W : Set E} {S X Y Z : Scheme.{0}}
    {p : Z ⟶ X} {q : Z ⟶ Y} {s : X ⟶ S} {t : Y ⟶ S} (H : IsPullback p q s t) {c : E → (Sp ℂ ⟶ Z)}
    (ha : IsHolTo W (fun w => c w ≫ p)) (hb : IsHolTo W (fun w => c w ≫ q)) : IsHolTo W c := by
  apply GlobalTheory.HolTorsion.isHolTo_of_isPullback <;> assumption

theorem isHolTo_fibPt {W : Set E} (hW : IsOpen W) {X : Scheme.{0}} (G : Over X) (y : Sp ℂ ⟶ X)
    (e : E → (Over.mk y ⟶ G)) (he : IsHolTo W (fun z => (e z).left)) :
    IsHolTo W (fun z => fibPt G (e z)) := by
  refine isHolTo_of_isPullback (IsPullback.of_hasPullback G.hom y) ?_ ?_
  · simpa only [fibPt, pullback.lift_fst] using he
  · simpa only [fibPt, pullback.lift_snd] using isHolTo_const hW _

theorem isHolTo_fibPt_and_comp :
    ∀ (X : Scheme.{0}) (G : Over X) (y : Sp ℂ ⟶ X) (g : ℕ) (e : (Fin g → ℂ) → (Over.mk y ⟶ G)), IsHolTo Set.univ (fun z => (e z).left) → IsHolTo Set.univ (fun z => fibPt G (e z)) ∧ ∀ (Y : Scheme.{0}) (ψ : pullback G.hom y ⟶ Y), IsHolTo Set.univ (fun z => fibPt G (e z) ≫ ψ) :=
  fun _ G y _ e he =>
    ⟨isHolTo_fibPt isOpen_univ G y e he, fun _ ψ => isHolTo_comp (isHolTo_fibPt isOpen_univ G y e he) ψ⟩

end GlobalTheory.HolFibre
