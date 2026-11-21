import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Brauer
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.RealTransport.RealTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Langlands
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.BcDualOfPolarized
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published UpperTheory.V.Af.Bc GlobalTheory.RealGal
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BcPolar

theorem exists_sign_twist {K : Type} [Field K] [NumberField K] [IsCMField K] (χ : HChar (maximalRealSubfield K))
    (h : ∀ v v' : InfinitePlace (maximalRealSubfield K), χ.locInf v (-1) = χ.locInf v' (-1)) (b : ℤ) :
    ∃ k : ℕ, ∀ v, (χ * quadChar K ^ k).locInf v (-1) = (-1) ^ b := by
  obtain ⟨v₀⟩ : Nonempty (InfinitePlace (maximalRealSubfield K)) := inferInstance
  have hval : ∀ (k : ℕ) v, (χ * quadChar K ^ k).locInf v (-1) = χ.locInf v₀ (-1) * (-1) ^ k := fun k v => by
    rw [HChar.locInf_mul, locInf_pow, quadChar_locInf, h v v₀]
  have h2 : χ.locInf v₀ (-1) ^ 2 = 1 := by rw [← map_pow, neg_one_sq, map_one]
  have h3 : ((χ.locInf v₀ (-1) : ℂˣ) : ℂ) ^ 2 = 1 := by rw [← Units.val_pow_eq_pow_val, h2, Units.val_one]
  simp only [hval, Units.ext_iff, Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, Units.val_neg,
    Units.val_one]
  rcases sq_eq_one_iff.1 h3 with e | e <;> rcases Int.even_or_odd b with hb' | hb' <;> rw [e, hb'.neg_one_zpow]
  · exact ⟨0, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨1, fun _ => by simp⟩
  · exact ⟨0, fun _ => by simp⟩

end GlobalTheory.BcPolar
