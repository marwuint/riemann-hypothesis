import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsCptGen

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.CptInh

open AlgebraicGeometry CategoryTheory GlobalTheory.CompanionTheory.Ar

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

theorem dom (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (p : Cpt ξ) :
    IsDomain (X.presheaf.stalk p.1) := by
  exact Function.Injective.isDomain (genMap ξ p) (h.inj p)

theorem nogen (ξ : Spec (CommRingCat.of Ω) ⟶ X) (h : IsCptGen ξ) (y : X) (hy : y ⤳ genPt ξ) :
    y = genPt ξ := by
  have hy' : y ∈ Set.range (X.fromSpecStalk (genPt ξ)) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  obtain ⟨q, hq⟩ := hy'
  obtain ⟨f, hf⟩ : ∃ f : X.presheaf.stalk (genPt ξ) →+* Ω, Function.Bijective f :=
    ⟨(Scheme.stalkClosedPointTo ξ).hom, h.bij⟩
  have hmax : ∀ x ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk (genPt ξ)), x = 0 := by
    intro x hx
    by_contra hne
    have h1 : f x ≠ 0 := by
      intro h0
      apply hne
      apply hf.1
      rw [h0, map_zero]
    obtain ⟨v, hv⟩ := hf.2 (f x)⁻¹
    have hxv : x * v = 1 := hf.1 (by rw [map_mul, hv, mul_inv_cancel₀ h1, map_one])
    exact mem_nonunits_iff.mp ((IsLocalRing.mem_maximalIdeal x).mp hx) (IsUnit.of_mul_eq_one v hxv)
  have hq' : q = IsLocalRing.closedPoint (X.presheaf.stalk (genPt ξ)) := by
    apply PrimeSpectrum.ext
    apply le_antisymm
    · exact IsLocalRing.le_maximalIdeal (PrimeSpectrum.isPrime q).ne_top
    · intro x hx
      rw [hmax x hx]
      exact zero_mem _
  rw [← hq, hq']
  exact Scheme.fromSpecStalk_closedPoint

end GlobalTheory.CompanionTheory.Ar.CptInh
