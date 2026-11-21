import Formalism.SharpRestriction.InertJacobiLevels.ExtraNum
import Formalism.ThetaLiftIndependence.Statement
import Formalism.HermitianLattices.StatementMass
import Formalism.ThetaLiftIndependence.ThetaOrbitSums.ClassRepsDefinite
import Formalism.HermitianLattices.HermitianLatticesProofs.MassBasic

noncomputable section

open NumberField

namespace Formalism.MainNotions.Gaps.MI

open Formalism.MainNotions.Inhab Formalism.BasicNotions Formalism.MainNotions.StandardLattice

section Std

variable (K : Type) [Field K] [NumberField K] [StarRing K]

theorem stdForm_apply' (n : ℕ) (x y : Fin n → K) :
    stdForm K n x y = ∑ i, star (x i) * y i := rfl

variable (hc : ∀ (φ : K →+* ℂ) (a : K), φ (star a) = starRingEnd ℂ (φ a))

end Std

end Formalism.MainNotions.Gaps.MI
