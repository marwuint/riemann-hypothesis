import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensIdxH

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes PI.VolFromSW
  IsLocalRing

namespace IdxHW

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]
  (b : Module.Basis (Fin 2) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E) (a : ℕ)

def cr (y : Fv F v ⊗[F] E) (k : Fin 2) : Fv F v := (Algebra.TensorProduct.basis (Fv F v) b).repr y k

theorem crdS_eq (S : HermR (Fv F v) σ a) (i j : Fin a) (k : Fin 2) :
    crdS b v σ a S i j k = cr b v ((S : Matrix (Fin a) (Fin a) (Fv F v ⊗[F] E)) i j) k := rfl

end Main

end IdxHW

end PI.VolStabSW
