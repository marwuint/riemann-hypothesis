import Formalism.WachLatticeTwists.SandwichH1Classes.PerturbationForEveryTwist

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

variable {ℓ : ℕ} [Fact ℓ.Prime] (Tt : TateTr ℓ) {r : ℕ}

lemma Vi_apply (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (j : ℤ) (t q : Fin r) :
    Tt.Vi Vm w j t q = algebraMap ℤ_[ℓ] Tt.Om ((w ^ j : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) * Vm q t := rfl

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
