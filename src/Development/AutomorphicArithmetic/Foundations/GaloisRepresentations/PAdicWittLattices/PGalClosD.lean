module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.SplitsBasic
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.IsAdmissibleIntegralBasisChangeOne
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PChart
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFibFin
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
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
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

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

namespace UpperTheory.Gal.G3

private theorem fibre_finite {Y Z : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] (Ω : Type) [Field Ω] (x : sp Ω ⟶ Z) :
    Finite {y : sp Ω ⟶ Y // y ≫ s = x} := by
  have h := UpperTheory.Gal.TranscendenceTraces.fibFin_of UpperTheory.Gal.TranscendenceTraces.chart_of s Ω x
  exact h.to_subtype

private theorem epi_of_field {Ω Ω' : Type} [Field Ω] [Field Ω'] (x : sp Ω' ⟶ sp Ω) : Epi x := by
  exact Flat.epi_of_flat_of_surjective x

private theorem point_over {Z : Scheme.{0}} (z : Z) :
    ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : sp Ω ⟶ Z), x (IsLocalRing.closedPoint Ω) = z := by
  refine ⟨AlgebraicClosure (Z.residueField z), inferInstance, inferInstance,
    Spec.map (CommRingCat.ofHom (algebraMap (Z.residueField z) (AlgebraicClosure (Z.residueField z)))) ≫
      Z.fromSpecResidueField z, ?_⟩
  exact Scheme.fromSpecResidueField_apply z _

end UpperTheory.Gal.G3

private theorem exists_comp_sigma_eq_of_comp_eq_comp {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] {d : ℕ}
    (hd : ∀ (K : Type) [Field K] [IsAlgClosed K] (x : Spec (CommRingCat.of K) ⟶ Z),
      Nat.card {y // y ≫ s = x} = d)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] (x : UpperTheory.Gal.G3.sp Ω ⟶ W) (y : UpperTheory.Gal.G3.sp Ω ⟶ Y)
    (hy : y ≫ s = x ≫ c) :
    ∃ j, x ≫ σ j = y := by
  have hfin := UpperTheory.Gal.G3.fibre_finite s Ω (x ≫ c)
  let f : Fin d → {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x ≫ c} :=
    fun j => ⟨x ≫ σ j, by rw [Category.assoc, hσ]⟩
  have hf : Function.Injective f := fun i j hij => hinj Ω x (congrArg Subtype.val hij)
  have hb := hf.bijective_of_nat_card_le (by rw [hd Ω (x ≫ c), Nat.card_eq_fintype_card, Fintype.card_fin])
  obtain ⟨j, hj⟩ := hb.2 ⟨y, hy⟩
  exact ⟨j, congrArg Subtype.val hj⟩

theorem UpperTheory.Gal.G3.pGalClosD :
    SplitsPts → OrdEx → GalClosD := by
  intro hS hO Z Y s d hF
  obtain ⟨hfin, het, hd⟩ := hF
  obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := hO s d
  have hex : ∀ g : Equiv.Perm (Fin d), ∃! w : W ⟶ W, w ≫ c = c ∧ ∀ j, w ≫ σ j = σ (g j) := by
    intro g
    refine huniv W c (fun j => σ (g j)) (fun j => hσ (g j)) ?_
    intro Ω _ x i j hij
    exact g.injective (hinj Ω x hij)
  choose a ha using fun g => (hex g).exists
  have hone : a 1 = 𝟙 W :=
    (hex 1).unique (ha 1) ⟨Category.id_comp c, fun j => by simp⟩
  have hmul : ∀ g h, a (g * h) = a g ≫ a h := by
    intro g h
    refine (hex (g * h)).unique (ha (g * h)) ⟨?_, fun j => ?_⟩
    · rw [Category.assoc, (ha h).1, (ha g).1]
    · rw [Category.assoc, (ha h).2 j, (ha g).2 (h j)]
      rfl
  have hspl : Splits s c σ := by
    refine hS s c (Fin d) σ hσ ?_
    intro Ω _ _ x y hy
    obtain ⟨j, hj⟩ := exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x y hy
    exact ⟨j, hj, fun j' hj' => hinj Ω x (hj'.trans hj.symm)⟩
  have hsur : Surjective c := by
    constructor
    intro z
    obtain ⟨Ω, _, _, x, hx⟩ := UpperTheory.Gal.G3.point_over z
    have hfF := UpperTheory.Gal.G3.fibre_finite s Ω x
    have hcard : Nat.card {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x} = d := hd Ω x
    let e := Finite.equivFin {y : UpperTheory.Gal.G3.sp Ω ⟶ Y // y ≫ s = x}
    let yy : Fin d → (UpperTheory.Gal.G3.sp Ω ⟶ Y) := fun j => (e.symm (Fin.cast hcard.symm j)).1
    have hyy : ∀ j, yy j ≫ s = x := fun j => (e.symm (Fin.cast hcard.symm j)).2
    have hinj' : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ yy j := by
      intro Ω' _ x' i j hij
      haveI := UpperTheory.Gal.G3.epi_of_field x'
      have h1 : yy i = yy j := (cancel_epi x').1 hij
      exact Fin.cast_injective _ (e.symm.injective (Subtype.val_injective h1))
    obtain ⟨w, ⟨hw, _⟩, _⟩ := huniv (UpperTheory.Gal.G3.sp Ω) x yy hyy hinj'
    refine ⟨w (IsLocalRing.closedPoint Ω), ?_⟩
    rw [← hx, ← hw]
    rfl
  have hgal : Splits c c a := by
    refine hS c c (Equiv.Perm (Fin d)) a (fun g => (ha g).1) ?_
    intro Ω _ _ x y hy
    have hpt : ∀ j, ∃ k, x ≫ σ k = y ≫ σ j := by
      intro j
      exact exists_comp_sigma_eq_of_comp_eq_comp s hd c σ hσ hinj Ω x (y ≫ σ j) (by rw [Category.assoc, hσ, hy])
    choose p hp using hpt
    have hpi : Function.Injective p := by
      intro i j hij
      apply hinj Ω y
      simp only
      rw [← hp i, ← hp j, hij]
    let g := Equiv.ofBijective p (Finite.injective_iff_bijective.1 hpi)
    have hinjy : ∀ (Ω' : Type) [Field Ω'] (x' : UpperTheory.Gal.G3.sp Ω' ⟶ UpperTheory.Gal.G3.sp Ω),
        Function.Injective fun j => x' ≫ (y ≫ σ j) := by
      intro Ω' _ x' i j hij
      apply hinj Ω' (x' ≫ y)
      simpa only [Category.assoc] using hij
    refine ⟨g, ?_, ?_⟩
    · refine (huniv (UpperTheory.Gal.G3.sp Ω) (x ≫ c) (fun j => y ≫ σ j)
        (fun j => by rw [Category.assoc, hσ, hy]) hinjy).unique ⟨?_, fun j => ?_⟩ ⟨hy, fun j => rfl⟩
      · rw [Category.assoc, (ha g).1]
      · rw [Category.assoc, (ha g).2 j]
        exact hp j
    · intro g' hg'
      refine Equiv.ext fun j => ?_
      apply hinj Ω x
      simp only
      rw [← (ha g').2 j, ← Category.assoc, hg', ← hp j]
      rfl
  exact ⟨W, c, Equiv.Perm (Fin d), inferInstance, inferInstance, a, σ,
    ⟨hcf, hce, hsur, hone, hmul, hgal⟩, hspl⟩
