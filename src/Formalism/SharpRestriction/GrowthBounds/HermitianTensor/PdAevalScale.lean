import Formalism.SharpRestriction.GrowthBounds.HermitianTensor.DetFactsPAlt

noncomputable section

namespace Formalism.MainNotions.flipOneThree.Pf

open Formalism.MainNotions.G Formalism.MainNotions.flipOneThree Formalism.CountingSumsFrames Formalism.GradedWeylDivisibility MvPolynomial

variable (A : Type) [CommRing A] (r : ℕ)

theorem detY_eq : detY A r = (genY A r).det := rfl

end Formalism.MainNotions.flipOneThree.Pf

end
