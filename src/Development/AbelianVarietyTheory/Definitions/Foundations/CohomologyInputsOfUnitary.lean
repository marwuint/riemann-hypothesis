import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormUnitPowSubOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CyclotomicCharInertiaSurjective

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV
open scoped Matrix

namespace GlobalTheory.Ord2.Test

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] {l : ℕ} [Fact l.Prime]

theorem isConj_iff (s : G ℚ Ω) : IsConj s ↔ IsCC s := Iff.rfl

theorem eps_eq (s : G ℚ Ω) : eps l s = algebraMap ℤ_[l] (Qbar l) (cycZ ℚ Ω l s : ℤ_[l]) := rfl

theorem cycZ_ine [IsAlgClosure ℚ Ω] {v : Pl} (hl : ((l : ℕ) : 𝓞 ℚ) ∉ v.asIdeal) {A : ValuationSubring Ω}
    (hA : IsPlaceOver A v) {σ : G ℚ Ω} (hσ : σ ∈ Ine (F := ℚ) A) : cycZ ℚ Ω l σ = 1 := by
  refine Units.ext (PadicInt.ext_of_toZModPow.mp fun n => ?_)
  rw [cycZ_toZModPow_eq hl hA (q := 1) (fun x hx => by simpa using hσ.2 x hx) n]
  simp

theorem nu (u : ℤ_[l]ˣ) : ‖((u : ℤ_[l]) : ℚ_[l])‖ = 1 := PadicInt.norm_units u

end GlobalTheory.Ord2.Test

end
