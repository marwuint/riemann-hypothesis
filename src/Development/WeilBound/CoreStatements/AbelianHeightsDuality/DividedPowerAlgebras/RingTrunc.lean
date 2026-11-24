module

import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDPMorphismOfIsStd
public import Development.AbelianVarietyTheory.Definitions.Divisors.RatBasisLinearIndependentInt
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.ExistsDividedPowersAug
public import Development.WeilBound.CoreStatements.AbelianHeightsDuality.DividedPowerAlgebras.FilIsSubDPIdeal
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
import Mathlib.RingTheory.WittVector.IsPoly
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

set_option autoImplicit false

noncomputable section

open DividedPowers GlobalTheory.Cris GlobalTheory.PDA

namespace FubiniStudyChowHeightFormula₂.Adr

variable {R B : Type} [CommRing R] [CommRing B] {I : Ideal R} {J : Ideal B}

def ExtDP (κ : DividedPowers I) (f : R →+* B) (δ : DividedPowers J) : Prop :=
  ∃ δ' : DividedPowers (J ⊔ I.map f), IsDPMorphism δ δ' (RingHom.id B) ∧ IsDPMorphism κ δ' f

theorem ExtDP.of_eq {κ : DividedPowers I} {f : R →+* B} {δ : DividedPowers J} {J' : Ideal B}
    (δ' : DividedPowers J') (h : J' = J ⊔ I.map f) (h₁ : IsDPMorphism δ δ' (RingHom.id B))
    (h₂ : IsDPMorphism κ δ' f) : ExtDP κ f δ := by
  subst h
  exact ⟨δ', h₁, h₂⟩

theorem dp_of_std (δ : DividedPowers J) (Q : PDPoly B) (η : DividedPowers (Q.ext J)) (hQ : Q.IsStd δ η)
    {C : Type} [CommRing C] {L : Ideal C} (θ : DividedPowers L) (F : Q.P →+* C) (c : C) (hc : c ∈ L)
    (hF : IsDPMorphism δ θ (F.comp (algebraMap B Q.P))) (he : ∀ n, F (Q.e n) = θ.dpow n c) :
    IsDPMorphism η θ F := by
  apply GlobalTheory.PDA.PDPoly.isDPMorphism_of_isStd <;> assumption

theorem ring_trunc (κ : DividedPowers I) (f : R →+* B) (δ : DividedPowers J) (h : ExtDP κ f δ) (n : ℕ)
    (hn : 1 ≤ n) : ∃ (A : Type) (_ : CommRing A) (a : B →+* A) (JA : Ideal A) (θ : DividedPowers JA),
      IsDPMorphism δ θ a ∧ IsLev θ n ∧ ExtDP κ (a.comp f) θ ∧ Function.Surjective a ∧
      ∀ (C : Type) [CommRing C] (L : Ideal C) (η : DividedPowers L), IsLev η n → ∀ g : B →+* C,
        IsDPMorphism δ η g → ∃ G : A →+* C, IsDPMorphism θ η G ∧ G.comp a = g := by
  obtain ⟨δ', h₁, h₂⟩ := h
  have hsub := Fil.fil_isSubDPIdeal δ n hn
  obtain ⟨θ, hθ, huniv⟩ := Fil.exists_quot δ (fil δ n) hsub
  have hsub' : δ'.IsSubDPIdeal (fil δ n) := by
    refine ⟨hsub.isSubideal.trans le_sup_left, ?_⟩
    intro m hm j hj
    have hjJ : j ∈ J := hsub.isSubideal hj
    have hj' := h₁.dpow_comp (n := m) j hjJ
    simp only [RingHom.id_apply] at hj'
    rw [hj']
    exact hsub.dpow_mem m hm hj
  obtain ⟨δ'', hδ'', -⟩ := Fil.exists_quot δ' (fil δ n) hsub'
  refine ⟨B ⧸ fil δ n, inferInstance, Ideal.Quotient.mk _, _, θ, hθ, ?_, ?_, Ideal.Quotient.mk_surjective, ?_⟩
  · show fil θ n = ⊥
    apply eq_bot_iff.mpr
    refine (Fil.fil_le_map_fil B J δ _ _ θ _ hθ rfl n).trans ?_
    rw [Ideal.map_quotient_self]
  · refine ExtDP.of_eq δ'' ?_ ?_ ?_
    · rw [Ideal.map_sup, Ideal.map_map]
    · apply huniv
      simpa using IsDPMorphism.comp δ'' hδ'' h₁
    · exact IsDPMorphism.comp δ'' hδ'' h₂
  · intro C _ L η hη g hg
    have hker : ∀ x ∈ fil δ n, g x = 0 := by
      intro x hx
      have h3 : g x ∈ fil η n := Fil.map_fil_le δ η g hg n (Ideal.mem_map_of_mem g hx)
      rw [show fil η n = ⊥ from hη] at h3
      exact (Ideal.mem_bot).mp h3
    refine ⟨Ideal.Quotient.lift _ g hker, ?_, Ideal.Quotient.lift_comp_mk _ g hker⟩
    apply huniv
    rwa [Ideal.Quotient.lift_comp_mk]

theorem ring_poly (κ : DividedPowers I) (f : R →+* B) (δ : DividedPowers J) (h : ExtDP κ f δ) :
    ∃ (A : Type) (_ : CommRing A) (a : B →+* A) (JA : Ideal A) (θ : DividedPowers JA) (y : A),
      IsDPMorphism δ θ a ∧ ExtDP κ (a.comp f) θ ∧ y ∈ JA ∧
      (∀ (C : Type) [CommRing C] (L : Ideal C) (η : DividedPowers L) (g : B →+* C),
        IsDPMorphism δ η g → ∀ z ∈ L, ∃ G : A →+* C, IsDPMorphism θ η G ∧ G.comp a = g ∧ G y = z) ∧
      ∀ (C : Type) [CommRing C] (G G' : A →+* C), G.comp a = G'.comp a →
        (∀ m, G (θ.dpow m y) = G' (θ.dpow m y)) → G = G' := by
  obtain ⟨δ', h₁, h₂⟩ := h
  obtain ⟨η, hQ⟩ := exists_std B J δ (stdPoly B)
  obtain ⟨η', hQ'⟩ := exists_std B _ δ' (stdPoly B)
  have h1 : (stdPoly B).e 1 ∈ (stdPoly B).ext J := (stdPoly B).e_one_mem_ext J
  refine ⟨(stdPoly B).P, inferInstance, algebraMap B (stdPoly B).P, (stdPoly B).ext J, η, (stdPoly B).e 1,
    hQ.dp, ?_, h1, ?_, ?_⟩
  · refine ExtDP.of_eq η' ?_ ?_ ?_
    · simpa only [PDPoly.ext, Ideal.map_sup, Ideal.map_map] using sup_right_comm _ _ _
    · refine dp_of_std δ (stdPoly B) η hQ η' (RingHom.id _) ((stdPoly B).e 1) ((stdPoly B).e_one_mem_ext _) ?_ ?_
      · simpa using IsDPMorphism.comp η' hQ'.dp h₁
      · intro m
        rw [hQ'.var m]
        rfl
    · exact IsDPMorphism.comp η' hQ'.dp h₂
  · intro C _ L ηC g hg z hz
    obtain ⟨G, hG1, hG2⟩ := Fil.exists_lift (stdPoly B) C g (fun m => ηC.dpow m z) (ηC.dpow_zero hz)
      (fun m k => ηC.mul_dpow hz)
    have hGa : G.comp (algebraMap B (stdPoly B).P) = g := RingHom.ext hG1
    refine ⟨G, dp_of_std δ (stdPoly B) η hQ ηC G z hz (by rw [hGa]; exact hg) hG2, hGa, ?_⟩
    rw [hG2 1]
    exact ηC.dpow_one hz
  · intro C _ G G' hGG' hm
    ext p
    have hp : p ∈ Submodule.span B (Set.range (stdPoly B).e) := by
      rw [(stdPoly B).e.span_eq]
      trivial
    induction hp using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨m, rfl⟩ := hx
      have hm' := hm m
      rwa [hQ.var] at hm'
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _), map_add (f := _), hx, hy]
    | smul b x _ hx =>
      rw [Algebra.smul_def, map_mul, map_mul, hx]
      congr 1
      exact RingHom.congr_fun hGG' b

theorem ring_adj (κ : DividedPowers I) (f : R →+* B) (δ : DividedPowers J) (h : ExtDP κ f δ) (n : ℕ)
    (hn : 1 ≤ n) :
    ∃ (A : Type) (_ : CommRing A) (a : B →+* A) (JA : Ideal A) (θ : DividedPowers JA) (y : A),
      IsDPMorphism δ θ a ∧ IsLev θ n ∧ ExtDP κ (a.comp f) θ ∧ y ∈ JA ∧
      ∀ (C : Type) [CommRing C] (L : Ideal C) (η : DividedPowers L), IsLev η n → ∀ g : B →+* C,
        IsDPMorphism δ η g → ∀ z ∈ L, ∃! G : A →+* C, IsDPMorphism θ η G ∧ G.comp a = g ∧ G y = z := by
  obtain ⟨A1, _, a1, JA1, θ1, y1, ha1, hext1, hy1, huniv1, huniq1⟩ := ring_poly κ f δ h
  obtain ⟨A2, _, a2, JA2, θ2, ha2, hlev, hext2, hsurj, huniv2⟩ := ring_trunc κ (a1.comp f) θ1 hext1 n hn
  have hmem : a2 y1 ∈ JA2 := ha2.1 (Ideal.mem_map_of_mem a2 hy1)
  refine ⟨A2, inferInstance, a2.comp a1, JA2, θ2, a2 y1, IsDPMorphism.comp θ2 ha2 ha1, hlev, ?_, hmem, ?_⟩
  · rwa [RingHom.comp_assoc]
  · intro C _ L η hη g hg z hz
    obtain ⟨G1, hG1, hG1a, hG1y⟩ := huniv1 C L η g hg z hz
    obtain ⟨G, hG, hGa⟩ := huniv2 C L η hη G1 hG1
    have hGy : G (a2 y1) = z := by
      rw [← RingHom.comp_apply, hGa, hG1y]
    refine ⟨G, ⟨hG, ?_, hGy⟩, ?_⟩
    · rw [← RingHom.comp_assoc, hGa, hG1a]
    · rintro G' ⟨hG', hG'a, hG'y⟩
      have e1 : ∀ (H : A2 →+* C) (m : ℕ), IsDPMorphism θ2 η H → H (a2 y1) = z →
          (H.comp a2) (θ1.dpow m y1) = η.dpow m z := by
        intro H m hH hHy
        rw [RingHom.comp_apply, ← ha2.2 y1 hy1, ← hH.2 _ hmem, hHy]
      have key : G'.comp a2 = G.comp a2 := by
        apply huniq1 C
        · rw [RingHom.comp_assoc, RingHom.comp_assoc, hG'a, ← RingHom.comp_assoc, hGa, hG1a]
        · intro m
          rw [e1 G' m hG' hG'y, e1 G m hG hGy]
      ext x
      obtain ⟨w, rfl⟩ := hsurj x
      exact RingHom.congr_fun key w

end FubiniStudyChowHeightFormula₂.Adr
