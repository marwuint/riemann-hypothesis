import Development.AbelianVarietyTheory.Definitions.Divisors.NormSub

noncomputable section

open scoped TensorProduct

namespace GlobalTheory.LKTorus

section Functoriality

variable {k k' k'' : Type} [Field k] [Field k'] [Field k'']
  {A A' A'' : Type} [CommRing A] [CommRing A'] [CommRing A''] [Algebra k A] [Algebra k' A'] [Algebra k'' A'']

def fixMap (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a)) :
    fixU k c →* fixU k' c' where
  toFun a := ⟨Units.map φ.toMonoidHom a, by
    have h : c (a : Aˣ) = ((a : Aˣ) : A) := a.2
    show c' (φ ((a : Aˣ) : A)) = φ ((a : Aˣ) : A)
    rw [← hc, h]⟩
  map_one' := by ext; simp
  map_mul' a b := by ext; simp

@[simp] theorem fixMap_apply (c : A →ₐ[k] A) (c' : A' →ₐ[k'] A') (φ : A →+* A') (hc : ∀ a, φ (c a) = c' (φ a))
    (a : fixU k c) : (((fixMap c c' φ hc a : fixU k' c') : A'ˣ) : A') = φ ((a : Aˣ) : A) := rfl

end Functoriality

section Localisation

def locInv (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L] (c : L →ₐ[ℚ] L) :
    (S ⊗[ℚ] L) →ₐ[S] (S ⊗[ℚ] L) :=
  Algebra.TensorProduct.map (AlgHom.id S S) c

@[simp] theorem locInv_tmul (S : Type) [Field S] [CharZero S] {L : Type} [CommRing L] [Algebra ℚ L]
    (c : L →ₐ[ℚ] L) (s : S) (x : L) : locInv S c (s ⊗ₜ x) = s ⊗ₜ c x := rfl

end Localisation

end GlobalTheory.LKTorus
