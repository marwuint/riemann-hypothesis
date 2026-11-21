import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TrivV

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.EtC.PStep
open GlobalTheory.EtC

def TU (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] : Type :=
  {v : Um M B // p v.1}

theorem TU.comp_aux {M : ℕ} {B : Type} [CommRing B] (x y z : Fin M → B) (u u' : Bˣ) (h1 : x = (u : B) • y)
    (h2 : y = (u' : B) • z) : x = ((u' * u : Bˣ) : B) • z := by
  subst h1 h2
  rw [smul_smul, Units.val_mul, mul_comm]

instance (M : ℕ) (p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop) (B : Type) [CommRing B] :
    SmallCategory (TU M p B) where
  Hom v w := {u : Bˣ // v.1.1 = (u : B) • w.1.1}
  id v := ⟨1, by simp⟩
  comp f g := ⟨g.1 * f.1, TU.comp_aux _ _ _ _ _ f.2 g.2⟩
  id_comp f := Subtype.ext (mul_one _)
  comp_id f := Subtype.ext (one_mul _)
  assoc f g h := Subtype.ext (mul_assoc _ _ _).symm

def TU.map (M : ℕ) {p : ∀ {B : Type} [CommRing B], (Fin M → B) → Prop}
    (hp : ∀ {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) (v : Fin M → B), p v → p (f ∘ v))
    {B C : Type} [CommRing B] [CommRing C] (f : B →+* C) : TU M p B ⥤ TU M p C where
  obj v := ⟨(Um.map M f).obj v.1, hp f _ v.2⟩
  map {v w} u := ⟨Units.map (f : B →* C) u.1, by
    funext i
    have h := congrArg f (congrFun u.2 i)
    simp only [Pi.smul_apply, smul_eq_mul, map_mul] at h
    exact h⟩
  map_id v := Subtype.ext (map_one (Units.map (f : B →* C)))
  map_comp u u' := Subtype.ext (map_mul (Units.map (f : B →* C)) _ _)

end GlobalTheory.EtC.PStep

end
