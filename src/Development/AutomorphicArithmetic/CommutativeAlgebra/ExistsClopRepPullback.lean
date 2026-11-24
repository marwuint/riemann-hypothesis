module

public import Development.AutomorphicArithmetic.RepresentationRank.RepOfRank
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

@[expose] public section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory

namespace UpperTheory.ClopPullback

variable {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S)

private noncomputable def fwd (T' : Over S') :
    (T' ⊗ (Over.pullback t).obj G).left ⟶ ((Over.map t).obj T' ⊗ G).left :=
  pullback.lift (pullback.fst T'.hom (pullback.snd G.hom t))
    (pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t) (by
      have h := pullback.condition (f := T'.hom) (g := pullback.snd G.hom t)
      have h2 := pullback.condition (f := G.hom) (g := t)
      simp only [Over.map_obj_hom, Category.assoc, h2]
      rw [reassoc_of% h])

private noncomputable def bwd (T' : Over S') :
    ((Over.map t).obj T' ⊗ G).left ⟶ (T' ⊗ (Over.pullback t).obj G).left :=
  pullback.lift (pullback.fst (T'.hom ≫ t) G.hom)
    (pullback.lift (pullback.snd (T'.hom ≫ t) G.hom) (pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom)
      (by simpa using (pullback.condition (f := T'.hom ≫ t) (g := G.hom)).symm))
    (pullback.lift_snd _ _ _).symm

private theorem fwd_fst (T' : Over S') :
    fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom = pullback.fst T'.hom (pullback.snd G.hom t) :=
  pullback.lift_fst _ _ _

private theorem fwd_snd (T' : Over S') :
    fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t :=
  pullback.lift_snd _ _ _

private theorem bwd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) = pullback.fst (T'.hom ≫ t) G.hom :=
  pullback.lift_fst _ _ _

private theorem bwd_snd_fst (T' : Over S') :
    bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.fst G.hom t =
      pullback.snd (T'.hom ≫ t) G.hom := by
  unfold bwd
  erw [pullback.lift_snd_assoc, pullback.lift_fst]

private theorem fwd_bwd (T' : Over S') : fwd t G T' ≫ bwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.fst T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.fst T'.hom (pullback.snd G.hom t)
    rw [bwd_fst, fwd_fst, Category.id_comp]
  · show fwd t G T' ≫ bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) =
      𝟙 _ ≫ pullback.snd T'.hom (pullback.snd G.hom t)
    apply pullback.hom_ext
    · rw [Category.assoc, Category.assoc, Category.assoc, bwd_snd_fst, fwd_snd]
      exact (Category.id_comp _).symm
    · have hb : bwd t G T' ≫ pullback.snd T'.hom (pullback.snd G.hom t) ≫ pullback.snd G.hom t =
          pullback.fst (T'.hom ≫ t) G.hom ≫ T'.hom := by
        unfold bwd
        erw [pullback.lift_snd_assoc, pullback.lift_snd]
      rw [Category.assoc, Category.assoc, hb, ← Category.assoc, fwd_fst, pullback.condition]
      exact (Category.id_comp _).symm

private theorem bwd_fwd (T' : Over S') : bwd t G T' ≫ fwd t G T' = 𝟙 _ := by
  apply pullback.hom_ext
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.fst (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.fst (T'.hom ≫ t) G.hom
    rw [fwd_fst, bwd_fst, Category.id_comp]
  · show bwd t G T' ≫ fwd t G T' ≫ pullback.snd (T'.hom ≫ t) G.hom =
      𝟙 _ ≫ pullback.snd (T'.hom ≫ t) G.hom
    rw [fwd_snd, bwd_snd_fst, Category.id_comp]

private noncomputable def cmp :
    ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left ⟶ (Y ⊗ G).left :=
  pullback.map _ _ _ _ (pullback.fst Y.hom t) (pullback.fst G.hom t) t
    (by simp [pullback.condition]) (by simp [pullback.condition])

private theorem key {T' : Over S'} (y' : T' ⟶ (Over.pullback t).obj Y) :
    (y' ▷ (Over.pullback t).obj G).left ≫ cmp t G Y =
      fwd t G T' ≫ (((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left := by
  set x := ((Over.mapPullbackAdj t).homEquiv _ _).symm y' with hx
  have c1 : cmp t G Y ≫ pullback.fst Y.hom G.hom =
      pullback.fst ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst Y.hom t :=
    pullback.lift_fst _ _ _
  have c2 : cmp t G Y ≫ pullback.snd Y.hom G.hom =
      pullback.snd ((Over.pullback t).obj Y).hom ((Over.pullback t).obj G).hom ≫
        pullback.fst G.hom t :=
    pullback.lift_snd _ _ _
  have hxl : x.left = y'.left ≫ pullback.fst Y.hom t := by
    simp [hx, Over.mapPullbackAdj]
  apply pullback.hom_ext
  · rw [Category.assoc, c1, ← Category.assoc, Over.whiskerRight_left_fst, Category.assoc,
      Category.assoc, Over.whiskerRight_left_fst, ← Category.assoc, hxl]
    exact congrArg (· ≫ y'.left ≫ pullback.fst Y.hom t) (fwd_fst t G T').symm
  · rw [Category.assoc, c2, ← Category.assoc, Over.whiskerRight_left_snd, Category.assoc,
      Over.whiskerRight_left_snd]
    exact (fwd_snd t G T').symm

end UpperTheory.ClopPullback

open UpperTheory.ClopPullback

private theorem UpperTheory.preimage_comp_scheme_opens_of_pullback {X Y Z : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ Z) (W : Z.Opens) :
    (f ≫ g) ⁻¹ᵁ W = f ⁻¹ᵁ (g ⁻¹ᵁ W) := by
  simp

private theorem UpperTheory.isClosed_preimage_opens_of_isClosed {X Y : Scheme.{0}} (f : X ⟶ Y) {W : Y.Opens}
    (hW : IsClosed (W : Set Y)) : IsClosed ((f ⁻¹ᵁ W : X.Opens) : Set X) :=
  hW.preimage f.continuous

private theorem UpperTheory.preimage_preimage_eq_of_section {X Y : Scheme.{0}} (f : X ⟶ Y) (g : Y ⟶ X) (h : f ≫ g = 𝟙 X)
    (W : X.Opens) : f ⁻¹ᵁ (g ⁻¹ᵁ W) = W := by
  rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, h]
  simp

theorem UpperTheory.exists_clopRep_pullback :
    ∀ {S S' : Scheme.{0}} (t : S' ⟶ S) (G Y : Over S) (U : (Y ⊗ G).left.Opens), UpperTheory.RepresentationRank.Rep G Y U → ∃ U' : ((Over.pullback t).obj Y ⊗ (Over.pullback t).obj G).left.Opens, UpperTheory.RepresentationRank.Rep ((Over.pullback t).obj G) ((Over.pullback t).obj Y) U' := by
  intro S S' t G Y U hU
  refine ⟨cmp t G Y ⁻¹ᵁ U, UpperTheory.isClosed_preimage_opens_of_isClosed _ hU.1, ?_⟩
  intro T' V' hV'
  obtain ⟨y, hy, huniq⟩ := hU.2 ((Over.map t).obj T') (bwd t G T' ⁻¹ᵁ V')
    (UpperTheory.isClosed_preimage_opens_of_isClosed _ hV')
  have hpre : ∀ y' : T' ⟶ (Over.pullback t).obj Y,
      (y' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) =
        fwd t G T' ⁻¹ᵁ ((((Over.mapPullbackAdj t).homEquiv _ _).symm y' ▷ G).left ⁻¹ᵁ U) := by
    intro y'
    rw [← UpperTheory.preimage_comp_scheme_opens_of_pullback, key, UpperTheory.preimage_comp_scheme_opens_of_pullback]
  refine ⟨(Over.mapPullbackAdj t).homEquiv _ _ y, ?_, ?_⟩
  · show (((Over.mapPullbackAdj t).homEquiv _ _ y) ▷ (Over.pullback t).obj G).left ⁻¹ᵁ
        (cmp t G Y ⁻¹ᵁ U) = V'
    rw [hpre, Equiv.symm_apply_apply, hy]
    exact UpperTheory.preimage_preimage_eq_of_section _ _ (fwd_bwd t G T') V'
  · intro y'' hy''
    have hy2 : (y'' ▷ (Over.pullback t).obj G).left ⁻¹ᵁ (cmp t G Y ⁻¹ᵁ U) = V' := hy''
    have h1 : ((((Over.mapPullbackAdj t).homEquiv _ _).symm y'' ▷ G).left ⁻¹ᵁ U) =
        bwd t G T' ⁻¹ᵁ V' := by
      rw [← hy2, hpre, UpperTheory.preimage_preimage_eq_of_section _ _ (bwd_fwd t G T')]
    have h2 := huniq _ h1
    rw [← h2, Equiv.apply_symm_apply]
