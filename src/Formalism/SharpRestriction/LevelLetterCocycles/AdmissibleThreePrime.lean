import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType

noncomputable section

namespace Formalism.MainNotions.AdmissibleThreePrime

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

def TheoremThreePrime (D : D7) : Prop := ArithmeticCylinders.TheoremThreePrime D

abbrev redF (D : D7) (i : D.nd.Loc) (ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i)) :
    G D.host.E D.nd.Om →* GL (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i)) :=
  mapRep ((D.naut.kFbar i).comp (IsLocalRing.residue (D.nd.O i))) ρ

def LabelDegreeHypotheses (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (Sig : List (Formalism.BasicNotions.Part D.naut.CG)),
    (∃ x, HasParamX D.nd D.naut i x Sig) →
    (∀ (k : Fin 2) (v : D.nd.PlG k),
      (D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Sig (D.naut.plGw k v))).natDegree =
        D.naut.lpDim (isoLoc D.nd D.naut Sig (D.naut.plGw k v))) →
    IsCuspIso D.nd D.naut Sig →
    ∀ ρ : G D.host.E D.nd.Om →* GL (Fin D.R.r) (D.nd.O i), IsRepOfSig D.nd D.naut i Sig ρ →
    ∀ k : Fin 2, D.nd.l i ≠ D.host.g k →
      haveI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
      (∀ v : D.nd.PlG k, ∃ ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i),
        (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
          (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
        Matrix.charpoly ((redF D i ρ (D.ntypes.tg k v) : GL (Fin D.R.r) _) :
            Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
          ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
              (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
            fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x))).prod ∧
        ∃ φ : G D.host.E D.nd.Om,
          redF D i ρ (φ * D.ntypes.tg k v * φ⁻¹) = redF D i ρ (D.ntypes.tg k v) ^ D.host.g k) ∧
      (∀ w ∈ placesOver D.host.E (D.host.g k), TameGen D.nd (D.nd.plOm.1 w) (D.nd.gam0 i w) →
        ∃ (v : D.nd.PlG k) (j : Fin D.R.m) (ι : Formalism.CyclotomicNorms.Fbar (D.host.g k) →* Formalism.CyclotomicNorms.Fbar (D.nd.l i))
          (e₁ e₂ : ℤ), (e₁ = 1 ∨ e₁ = -1) ∧ (e₂ = 1 ∨ e₂ = -1) ∧
          (∀ x y : Formalism.CyclotomicNorms.Fbar (D.host.g k), x ≠ 0 → y ≠ 0 → (orderOf x).Coprime (D.nd.l i) →
            (orderOf y).Coprime (D.nd.l i) → ι x = ι y → x = y) ∧
          Matrix.charpoly ((redF D i ρ (D.nd.gam0 i w) : GL (Fin D.R.r) _) :
              Matrix (Fin D.R.r) (Fin D.R.r) (Formalism.CyclotomicNorms.Fbar (D.nd.l i))) =
            ((Formalism.CyclotomicNorms.rootsBar (D.naut.items₂ k (D.naut.plGw k v)
                (isoLoc D.nd D.naut Sig (D.naut.plGw k v)))).map
              fun x => X - C (ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i) x) ^ e₁)).prod ∧
          D.naut.kFbar i (IsLocalRing.residue (D.nd.O i) (chi1 D.nd i (D.nd.gam0 i w))) =
            ι (Formalism.CyclotomicNorms.primeToPart (D.nd.l i)
              (algebraMap (ZMod (D.host.g k)) (Formalism.CyclotomicNorms.Fbar (D.host.g k))
                ((D.nd.chiT k v j : (ZMod (D.host.g k))ˣ) : ZMod (D.host.g k)))) ^ e₂)

end Formalism.MainNotions.AdmissibleThreePrime
