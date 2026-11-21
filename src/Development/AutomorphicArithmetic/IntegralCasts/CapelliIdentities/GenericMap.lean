import Mathlib

open AlgebraicGeometry CategoryTheory

namespace UpperTheory.Reformulated.B.GenericMap

theorem aux1 {Ω : Type} [Field Ω] : IsLocalRing Ω :=
  inferInstance

noncomputable def genPt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : X :=
  ξ (@IsLocalRing.closedPoint Ω _ (aux1 (Ω := Ω)))

noncomputable def Cpt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) : Type :=
  {p : X // genPt ξ ⤳ p}

theorem aux4 {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : genPt ξ ⤳ p.val :=
  p.property

theorem aux5 {Ω : Type} [Field Ω] : IsLocalRing (CommRingCat.of Ω) :=
  aux1 (Ω := Ω)

noncomputable def genMap {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : X.presheaf.stalk p.val →+* Ω :=
  (X.presheaf.stalkSpecializes (aux4 ξ p) ≫
    @Scheme.stalkClosedPointTo X (CommRingCat.of Ω) (aux5 (Ω := Ω)) ξ).hom

noncomputable def regAt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Subring Ω :=
  (genMap ξ p).range

noncomputable def unitAt {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) (a : Ω) : Prop :=
  a ≠ 0 ∧ a ∈ regAt ξ p ∧ a⁻¹ ∈ regAt ξ p

noncomputable def InFibre {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : ℕ) (q : Cpt ξ) : Prop :=
  ¬unitAt ξ q (p : Ω)

noncomputable def Char0 {X : Scheme} {Ω : Type} [Field Ω]
    (ξ : Spec (CommRingCat.of Ω) ⟶ X) (p : Cpt ξ) : Prop :=
  ∀ r : ℕ, r.Prime → ¬InFibre ξ r p

namespace Hlp
private theorem units_nat {Ω : Type} [Field Ω] (S : Subring Ω)
    (hp : ∀ r : ℕ, r.Prime → ((r : Ω) ≠ 0 ∧ (r : Ω) ∈ S ∧ (r : Ω)⁻¹ ∈ S)) :
    ∀ n : ℕ, n ≠ 0 → ((n : Ω) ≠ 0 ∧ (n : Ω) ∈ S ∧ (n : Ω)⁻¹ ∈ S) := by
  intro n
  induction n using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _; simp [S.one_mem]
  | prime p hpp => intro _; exact hp p hpp
  | mul a b ha hb =>
    intro hab
    have ha0 : a ≠ 0 := fun h => hab (by simp [h])
    have hb0 : b ≠ 0 := fun h => hab (by simp [h])
    obtain ⟨a1, a2, a3⟩ := ha ha0
    obtain ⟨b1, b2, b3⟩ := hb hb0
    refine ⟨by push_cast; exact mul_ne_zero a1 b1, by push_cast; exact S.mul_mem a2 b2, ?_⟩
    push_cast; rw [mul_inv]; exact S.mul_mem a3 b3
end Hlp

theorem main {X : Scheme} {Ω : Type} [Field Ω]
    {ξ : Spec (CommRingCat.of Ω) ⟶ X} {q : Cpt ξ}
    (hq : Char0 ξ q) (n : ℕ) (hn : n ≠ 0) : unitAt ξ q (n : Ω) :=
  Hlp.units_nat (regAt ξ q) (fun r hr => not_not.mp (hq r hr)) n hn

end UpperTheory.Reformulated.B.GenericMap
