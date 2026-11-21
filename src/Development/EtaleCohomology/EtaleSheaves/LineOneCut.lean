import Development.EtaleCohomology.EtaleSheaves.LineHigh

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.LineOneCut

abbrev fib {A : Type} [CommRing A] [IsLocalRing A] {Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) : Scheme.{0} :=
  pullback p (cpt A)

def fibMap {A : Type} [CommRing A] [IsLocalRing A] {U Z : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z) :
    fib (ι ≫ p) ⟶ fib p :=
  pullback.map (ι ≫ p) (cpt A) p (cpt A) ι (𝟙 _) (𝟙 _) (by simp) (by simp)

def FibCover : Prop := ∀ (A : Type) [CommRing A] [IsLocalRing A] {Z U V : Scheme.{0}} (p : Z ⟶ Spec (CommRingCat.of A))
  (ι₁ : U ⟶ Z) (ι₂ : V ⟶ Z), IsOpenImmersion ι₁ → IsOpenImmersion ι₂ → Set.range ι₁ ∪ Set.range ι₂ = Set.univ →
  IsOpenImmersion (fibMap p ι₁) ∧ IsOpenImmersion (fibMap p ι₂) ∧ Set.range (fibMap p ι₁) ∪ Set.range (fibMap p ι₂) = Set.univ

def ChartAcyc : Prop := Hyp → ∀ (q : ℕ) (A : Type) [CommRing A] [IsLocalRing A] {Z U : Scheme.{0}}
  (p : Z ⟶ Spec (CommRingCat.of A)) (ι : U ⟶ Z), IsOpenImmersion ι → IsAffine U → AICSch Z → IsUnit (q : A) →
  Acyc q (sch.obj (fib (ι ≫ p)))

end LateralTheory.E.LineOneCut
