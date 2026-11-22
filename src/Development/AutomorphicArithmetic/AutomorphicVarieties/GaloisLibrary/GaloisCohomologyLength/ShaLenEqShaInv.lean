import Mathlib
import Development.AutomorphicArithmetic.CharacterBoxes.ExistsPageN
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.NonemptyH0GlobalEquivGaloisImage
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.InfUnram
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaInfl
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.GalTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.PlaceTransport
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.GaloisCohomologyLength.ShaAbsRes

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.GaloisCohomology

noncomputable section

namespace UpperTheory.V.LDataCardLeFinrank

section

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime]

theorem map_Sha (D : LData F Ω l) (e : ℤ) :
    (Sha D e).map (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) =
      ShaAbs ((qzTw D e).comp (toGS Ω _)) (Above F l) := by
  rw [← D.hS]
  exact shaInfl F Ω D.S D.A D.hA _ _ _ (contTw F Ω l D e).1

theorem injective_infl (D : LData F Ω l) (e : ℤ) :
    Function.Injective (resH1 (qzTw D e) (toGS Ω _) (continuous_toGS Ω _)) :=
  (infUnram F Ω _ _ _ _ (contTw F Ω l D e).1).1

theorem shaLen_eq_abs (D : LData F Ω l) (e : ℤ) :
    shaLen D e = Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) := by
  rw [← qzTw_comp_toGS D e, ← map_Sha]
  exact (Submodule.equivMapOfInjective _ (injective_infl D e) _).length_eq

variable {F' Ω' : Type} [Field F'] [NumberField F'] [Field Ω'] [Algebra F' Ω'] [IsAlgClosure F' Ω']

theorem length_ShaAbs_le (f : F ≃+* F') (e : ℤ) :
    Module.length ℤ_[l] (ShaAbs (qzG F Ω l e) (Above F l)) ≤
      Module.length ℤ_[l] (ShaAbs (qzG F' Ω' l e) (Above F' l)) := by
  let σ : Ω ≃+* Ω' := IsAlgClosure.equivOfEquiv Ω Ω' f
  have hσ : ∀ x, σ (algebraMap F Ω x) = algebraMap F' Ω' (f.toRingHom x) :=
    fun x => IsAlgClosure.equivOfEquiv_algebraMap Ω Ω' f x
  obtain ⟨φ, h1, h2, h3, -, h5⟩ := galTransport F Ω F' Ω' f.toRingHom σ hσ
  have e1 : (qzG F Ω l e).comp φ = qzG F' Ω' l e := by
    refine MonoidHom.ext fun g => LinearMap.ext fun x => ?_
    rw [MonoidHom.comp_apply, qzG_apply, qzG_apply, h3]
  rw [← e1]
  refine (shaAbsRes F Ω F' Ω' _ _ φ h1 (fun v' A' hA' => ?_) _ _ _).2 (h5 f.surjective)
  obtain ⟨v, A, a, b, -, c, d⟩ := placeTransport F Ω F' Ω' f.toRingHom σ hσ φ h2 v' A' hA'
  exact ⟨v, A, a, b l, fun g hg => (c g).2 hg, fun g hg => (d g).2 hg⟩

theorem shaLen_eq_shaInv (D : LData F Ω l) (e : ℤ) : shaLen D e = shaInv F l e := by
  rw [shaLen_eq_abs]
  exact le_antisymm (length_ShaAbs_le (RingEquiv.refl F) e) (length_ShaAbs_le (RingEquiv.refl F) e)

theorem shaInv_congr (f : F ≃+* F') (e : ℤ) : shaInv F l e = shaInv F' l e :=
  le_antisymm (length_ShaAbs_le f e) (length_ShaAbs_le f.symm e)

end

end UpperTheory.V.LDataCardLeFinrank

end
