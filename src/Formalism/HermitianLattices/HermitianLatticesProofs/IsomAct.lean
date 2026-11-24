module

public import Formalism.HermitianLattices.StatementLat
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
import Mathlib.RingTheory.Coalgebra.CoassocSimps
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
import Mathlib.Tactic.TypeStar
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Module

noncomputable section

namespace Formalism.HermitianLatticesTheory

section SlopeTestRemainingChoices

variable {R K V : Type*} [CommRing R] [Field K] [StarRing K] [Algebra R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem isomAct_mem_gmap (g : V ≃ₗ[K] V) (L : Submodule R V) (x : V) :
    x ∈ gmap g L ↔ g.symm x ∈ L := by
  unfold gmap
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa using hy
  · exact fun hx => ⟨g.symm x, hx, by simp⟩

theorem isomAct_smul (g : V ≃ₗ[K] V) (s : R) (x : V) : g (s • x) = s • g x := by
  exact map_smul ((g : V →ₗ[K] V).restrictScalars R) s x

theorem isomAct_gmap_symm (g : V ≃ₗ[K] V) (L : Submodule R V) :
    gmap g.symm (gmap g L) = L := by
  ext x
  simp [isomAct_mem_gmap]

theorem isomAct_mem_dual (h : V →ₗ⋆[K] V →ₗ[K] K) (L : Submodule R V) (x : V) :
    x ∈ dual h L ↔ ∀ y ∈ L, h y x ∈ (1 : Submodule R K) := by
  simp only [dual, Formalism.E.hdual, Submodule.mem_iInf, Submodule.mem_comap,
    LinearMap.restrictScalars_apply]

theorem isomAct_lattice (g : V ≃ₗ[K] V) (L : Submodule R V) (hL : Submodule.IsLattice K L) :
    Submodule.IsLattice K (gmap g L) := by
  have e : ((gmap g L : Submodule R V) : Set V) = (g : V →ₗ[K] V) '' (L : Set V) := by
    ext x
    simp [gmap]
  refine ⟨hL.fg.map _, ?_⟩
  rw [e]
  intro s hs hli
  change s ⊆ ⇑g '' _ at hs
  have hpre := Set.preimage_mono (f := ⇑g) hs
  rw [Set.preimage_image_eq _ g.injective] at hpre
  rw [← Set.image_preimage_eq s g.surjective] at hli ⊢
  exact (linearIndepOn_id_imageₛ_iff (f := g.toLinearMap) g.injective.injOn).2
    (hL.linearIndepOn _ hpre
      ((linearIndepOn_id_imageₛ_iff (f := g.toLinearMap.restrictScalars R)
        g.injective.injOn).1 hli))

theorem isomAct_mem_locS {W : Type*} [AddCommGroup W] [Module R W] (S : Submonoid R)
    (L : Submodule R W) (x : W) : x ∈ locS S L ↔ ∃ s ∈ S, s • x ∈ L := Iff.rfl

end SlopeTestRemainingChoices

theorem isomAct : IsomAct := by
  intro R K V _ _ _ _ _ _ _ _ h g hg L
  have iso : ∀ x y, h (g x) (g y) = h x y := hg
  have hmem : ∀ z ∈ L, g z ∈ gmap g L := fun z hz =>
    (isomAct_mem_gmap g L _).2 (by simpa using hz)
  have hdual : dual h (gmap g L) = gmap g (dual h L) := by
    ext x
    rw [isomAct_mem_gmap, isomAct_mem_dual, isomAct_mem_dual]
    constructor
    · intro H z hz
      rw [← iso z (g.symm x)]
      simpa using H (g z) (hmem z hz)
    · intro H y hy
      rw [isomAct_mem_gmap] at hy
      have e := H _ hy
      rw [← iso (g.symm y) (g.symm x)] at e
      simpa using e
  have hsat : ∀ S : Submonoid R, locS S (gmap g L) = gmap g (locS S L) := by
    intro S
    ext x
    simp only [isomAct_mem_gmap, isomAct_mem_locS, isomAct_smul]
  have hint_r : IsIntegralLat h (gmap g L) ↔ IsIntegralLat h L := by
    unfold IsIntegralLat
    refine ⟨fun H x hx y hy => ?_, fun H x hx y hy => ?_⟩
    · rw [← iso x y]
      exact H _ (hmem x hx) _ (hmem y hy)
    · rw [isomAct_mem_gmap] at hx hy
      have e := H _ hx _ hy
      rw [← iso (g.symm x) (g.symm y)] at e
      simpa using e
  have hunim : IsUnimodular h (gmap g L) ↔ IsUnimodular h L := by
    unfold IsUnimodular
    rw [hdual]
    refine ⟨fun H => ?_, fun H => by rw [H]⟩
    simpa only [isomAct_gmap_symm] using congrArg (gmap (R := R) g.symm) H
  have hlat : Submodule.IsLattice K (gmap g L) ↔ Submodule.IsLattice K L := by
    refine ⟨fun H => ?_, isomAct_lattice g L⟩
    have e := isomAct_lattice g.symm (gmap g L) H
    rwa [isomAct_gmap_symm] at e
  refine ⟨hdual, ?_, hint_r, hunim, hlat⟩
  intro p
  unfold loc
  exact hsat _

end Formalism.HermitianLatticesTheory
