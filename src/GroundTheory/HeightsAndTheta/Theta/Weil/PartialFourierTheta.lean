import Mathlib
import GroundTheory.HeightsAndTheta.Theta.AdelicFourier
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.WeilPolarization.WmSysObjects
import GroundTheory.GlobalFields.TateThesis.AdelicChar

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global NumberField MeasureTheory TensorProduct
open scoped NumberField.AdeleRing ComplexOrder

noncomputable section

section Alg

variable {R W : Type*} [CommRing R] [AddCommGroup W] [Module R W]

variable {P₁ P₂ Q₁ Q₂ : Type*} [AddCommGroup P₁] [Module R P₁] [AddCommGroup P₂] [Module R P₂]
  [AddCommGroup Q₁] [Module R Q₁] [AddCommGroup Q₂] [Module R Q₂]

namespace FourPieces

variable {ω : LinearMap.BilinForm R W}

end FourPieces

end Alg

section Inhabitants

variable (R : Type*) [CommRing R]

end Inhabitants

end

end GroundTheory.Heights₂.Theta
