import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BcDensEqOfGram

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FlagConnect

def Carries {B Y T : Scheme.{0}} (π : Y ⟶ B) {ι : Type} (E : ι → B.Modules) (n : ι → ℕ)
    (fl : ∀ a, Vert.Flag ((Scheme.Modules.pullback π).obj (E a)) (n a)) (g' : T ⟶ Y) (g : T ⟶ B) (w : g' ≫ π = g)
    (fl' : ∀ a, Vert.Flag ((Scheme.Modules.pullback g).obj (E a)) (n a)) : Prop :=
  ∀ a i, ∃ e : (Scheme.Modules.pullback g').obj ((fl a).F i) ≅ (fl' a).F i,
    e.hom ≫ (fl' a).ι i = (Scheme.Modules.pullback g').map ((fl a).ι i) ≫
      (Scheme.Modules.pullbackComp g' π).hom.app (E a) ≫ (Scheme.Modules.pullbackCongr w).hom.app (E a)

end GlobalTheory.FlagConnect

end
