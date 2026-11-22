import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.LevelSectionsExactKernelLocusOpen
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsSplitGaussChars
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ProjectiveLinePlaceTrivialOnConstants

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Flat

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

section General

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

structure FibreCurve (ξ : Spec (CommRingCat.of Ω) ⟶ X) (ϖ : Ω) where

  k : Type

  κ : Type
  [fk : Field k]
  [fκ : Field κ]
  [alg : Algebra k κ]
  fg : (⊤ : IntermediateField k κ).FG
  trdeg : Algebra.trdeg k κ = 1

  C : Crv.ACurve κ
  w_pos : ∀ i, 0 < C.w i
  triv : ∀ i (a : k), a ≠ 0 → C.v i (algebraMap k κ a) = 1
  all : ∀ W : ValuationSubring κ, W ≠ ⊤ → (∀ a : k, algebraMap k κ a ∈ W) → ∃! i, (C.v i).valuationSubring = W

  η : Spec (CommRingCat.of κ) ⟶ X
  η_spec : genPt ξ ⤳ centre η
  η_zero : ValAt ξ η ϖ 0

  z : ∀ i, Spec (CommRingCat.of (C.v i).valuationSubring) ⟶ X
  z_gen : ∀ i, Spec.map (CommRingCat.ofHom (C.v i).valuationSubring.subtype) ≫ z i = η

attribute [instance] FibreCurve.fk FibreCurve.fκ FibreCurve.alg

def FibreCurve.HasDeg {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) (L : Lat ξ Ω) (d : ℤ) : Prop :=
  ∃ (e : Ω) (f : Γ.C.I → Ω) (r : Γ.C.I → Γ.κ), L.IsGenAt ⟨centre Γ.η, Γ.η_spec⟩ e ∧
    (∀ i, ∃ h : genPt ξ ⤳ centre (Γ.z i), L.IsGenAt ⟨centre (Γ.z i), h⟩ (f i)) ∧
    (∀ i, r i ≠ 0 ∧ ValAt ξ Γ.η (e / f i) (r i)) ∧ {i | Γ.C.v i (r i) ≠ 1}.Finite ∧
    ∑ᶠ i, (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (r i))) = d

def NumTrivMod {ξ : Spec (CommRingCat.of Ω) ⟶ X} (L : Lat ξ Ω) (ϖ : Ω) : Prop :=
  ∀ Γ : FibreCurve ξ ϖ, Γ.HasDeg L 0

namespace FibreCurve

open ProjectiveLinePlaces

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X} {ϖ : Ω} (Γ : FibreCurve ξ ϖ) {L L' M : Lat ξ Ω} {d d' : ℤ}

theorem generic_centre_specializes (i : Γ.C.I) : centre Γ.η ⤳ centre (Γ.z i) := by
  have := centre_specializes (Γ.z i) (Γ.C.v i).valuationSubring.subtype
  rwa [Γ.z_gen i] at this

theorem z_spec (i : Γ.C.I) : genPt ξ ⤳ centre (Γ.z i) := Γ.η_spec.trans (Γ.generic_centre_specializes i)

theorem finite_support {g : Γ.C.I → Γ.κ} (hg : {i | Γ.C.v i (g i) ≠ 1}.Finite) :
    Function.HasFiniteSupport fun i => (Γ.C.w i : ℤ) * (-WithZero.log (Γ.C.v i (g i))) :=
  hg.subset fun i hi h1 => hi (by simp [h1])

theorem exists_val_of_unitAt (i : Γ.C.I) {a : Ω} (ha : unitAt ξ ⟨centre (Γ.z i), Γ.z_spec i⟩ a) :
    ∃ t : Γ.κ, ValAt ξ Γ.η a t ∧ Γ.C.v i t = 1 := by
  obtain ⟨t, ht⟩ := valAt_of_unit _ ha
  refine ⟨_, valAt_restrict _ (Γ.z_gen i) Γ.η_spec ht, ?_⟩
  have a1 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) ≤ 1 := t.1.2
  have a2 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) ≤ 1 := (t⁻¹).1.2
  have a3 : Γ.C.v i ((Γ.C.v i).valuationSubring.subtype t) *
      Γ.C.v i ((Γ.C.v i).valuationSubring.subtype ↑t⁻¹) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine le_antisymm a1 ?_
  calc (1 : WithZero (Multiplicative ℤ)) = _ := a3.symm
    _ ≤ _ * 1 := by gcongr
    _ = _ := mul_one _

variable {Γ}

theorem HasDeg.mul (hM : ∀ p e e', L.IsGenAt p e → L'.IsGenAt p e' → M.IsGenAt p (e * e'))
    (h : Γ.HasDeg L d) (h' : Γ.HasDeg L' d') : Γ.HasDeg M (d + d') := by
  obtain ⟨e, f, r, he, hf, hr, hfin, hd⟩ := h
  obtain ⟨e', f', r', he', hf', hr', hfin', hd'⟩ := h'
  refine ⟨e * e', fun i => f i * f' i, fun i => r i * r' i, hM _ _ _ he he', fun i => ?_, fun i => ⟨?_, ?_⟩,
    (hfin.union hfin').subset fun i hi => ?_, ?_⟩
  · obtain ⟨h, hi⟩ := hf i
    obtain ⟨_, hi'⟩ := hf' i
    exact ⟨h, hM _ _ _ hi hi'⟩
  · exact mul_ne_zero (hr i).1 (hr' i).1
  · rw [mul_div_mul_comm]
    exact CoordModel.valAt_mul (hr i).2 (hr' i).2
  · by_contra hc
    simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
    exact hi (by rw [map_mul, hc.1, hc.2, mul_one])
  · have : ∀ i, WithZero.log (Γ.C.v i (r i * r' i)) =
        WithZero.log (Γ.C.v i (r i)) + WithZero.log (Γ.C.v i (r' i)) := fun i => by
      rw [map_mul, WithZero.log_mul (by simpa using (hr i).1) (by simpa using (hr' i).1)]
    simp_rw [this, neg_add, mul_add]
    rw [finsum_add_distrib (Γ.finite_support hfin) (Γ.finite_support hfin'), hd, hd']

variable (Γ)

end FibreCurve

end General

end GlobalTheory.CompanionTheory.Ar.Flat
