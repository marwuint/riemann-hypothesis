module

public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCharacter
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsAdditiveOfUniversal
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
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.Style
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
import Development.AbelianVarietyTheory.Definitions.Divisors.SameIdIff

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.CharKer

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CharKer

variable {S : Scheme.{0}}

def pmap2 {A A' : Over S} (q : A ⟶ A') (T : Over S) : A ⊗ (A ⊗ T) ⟶ A' ⊗ (A' ⊗ T) :=
  lift (fst A (A ⊗ T) ≫ q) (snd A (A ⊗ T) ≫ pmap q T)

def ptFst (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T)

def ptSnd (A T : Over S) : A ⊗ (A ⊗ T) ⟶ A ⊗ T := lift (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)

def ptMul (A T : Over S) [MonObj A] : A ⊗ (A ⊗ T) ⟶ A ⊗ T :=
  lift (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T)

def addBundle {A T : Over S} [MonObj A] (M : LB (A ⊗ T).left) : LB (A ⊗ (A ⊗ T)).left :=
  LB.div (tens (ev M (fst A (A ⊗ T)) (snd A (A ⊗ T) ≫ snd A T))
      (ev M (snd A (A ⊗ T) ≫ fst A T) (snd A (A ⊗ T) ≫ snd A T)))
    (ev M (fst A (A ⊗ T) * (snd A (A ⊗ T) ≫ fst A T)) (snd A (A ⊗ T) ≫ snd A T))

theorem preimage_le_of_comp {X Y Z W : Scheme.{0}} {f : X ⟶ Y} {g : Y ⟶ W} {f' : X ⟶ Z} {g' : Z ⟶ W}
    (h : f ≫ g = f' ≫ g') (U : W.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ U) ≤ f' ⁻¹ᵁ (g' ⁻¹ᵁ U) := by
  intro x hx
  have e : g.base (f.base x) = g'.base (f'.base x) := by
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
  show g'.base (f'.base x) ∈ U
  rwa [← e]

theorem prodMapPairTimesIdentity_fst {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptFst A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptFst, pmap]

theorem prodMapPairTimesIdentity_snd {A A' : Over S} (q : A ⟶ A') (T : Over S) :
    (pmap2 q T).left ≫ (lift (snd A' (A' ⊗ T) ≫ fst A' T) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptSnd A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptSnd, pmap]

theorem prodMapPairTimesIdentity_mul {A A' : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (T : Over S) :
    (pmap2 q T).left ≫ (lift (fst A' (A' ⊗ T) * (snd A' (A' ⊗ T) ≫ fst A' T)) (snd A' (A' ⊗ T) ≫ snd A' T)).left =
      (ptMul A T).left ≫ (pmap q T).left := by
  rw [← Over.comp_left, ← Over.comp_left]
  congr 1
  ext <;> simp [pmap2, ptMul, pmap, MonObj.comp_mul, MonObj.mul_comp]

theorem addGen_le₁ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptFst A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.1 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_fst q T) _)
  exact fun x hx => LB.wchart_le M _ k.1.1 PUnit.unit hx.1.1

theorem addGen_le₂ {A A' T : Over S} [MonObj A'] (q : A ⟶ A') (M : LB (A' ⊗ T).left) (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptSnd A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.1.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_snd q T) _)
  exact fun x hx => LB.wchart_le M _ k.1.2 PUnit.unit hx.1.2

theorem addGen_le₃ {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (k : (addBundle M).ι) :
    (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k ≤ (ptMul A T).left ⁻¹ᵁ ((pmap q T).left ⁻¹ᵁ M.U (k.2 PUnit.unit)) := by
  refine le_trans ?_ (preimage_le_of_comp (prodMapPairTimesIdentity_mul q T) _)
  exact fun x hx => LB.wchart_le M _ k.2 PUnit.unit hx.2

def addGen {A A' T : Over S} [MonObj A] [MonObj A'] (q : A ⟶ A') [IsMonHom q] (M : LB (A' ⊗ T).left)
    (e : ∀ k, Γ((A ⊗ T).left, (pmap q T).left ⁻¹ᵁ M.U k)ˣ) (k : (addBundle M).ι) :
    Γ((A ⊗ (A ⊗ T)).left, (pmap2 q T).left ⁻¹ᵁ (addBundle M).U k)ˣ :=
  res (addGen_le₁ q M k) (pullU (ptFst A T).left _ (e (k.1.1 PUnit.unit))) *
    res (addGen_le₂ q M k) (pullU (ptSnd A T).left _ (e (k.1.2 PUnit.unit))) *
    (res (addGen_le₃ q M k) (pullU (ptMul A T).left _ (e (k.2 PUnit.unit))))⁻¹

end GlobalTheory.CharKer
