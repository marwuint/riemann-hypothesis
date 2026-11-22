import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice
import Formalism.SharpRestriction.GlobalSchurBounds.LocalCountingBounds
import Formalism.LocalToGlobal.BesselHermitianTheta.MinfDensity
import Formalism.LocalToGlobal.HermitianColumns.InLocalDiscriminantKernel
import Formalism.SharpRestriction.GlobalSchurBounds.QuadraticLogDerivCongr
import Formalism.SharpRestriction.GlobalSchurBounds.Chosen

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions
open scoped TensorProduct

def LandherrHasse (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    ∃ b : Fin W.rank → W.V, LinearIndependent D.host.E b ∧
      ∀ a c, W.hT (b a) (b c) = if a = c then 1 else 0

def GenusMassStd (D : D7) : Prop :=
  letI := D.host.cmStar
  ∀ W : HSpace D.host.E, W.SigOK → (∀ τ, W.sig τ = (W.rank, 0)) →
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.MainNotions.StandardLattice.massI D W.rank

def Link4p : Prop := ∀ (D : D7) (Lv : LevelData D), Formalism.MainNotions.StandardLattice.Conclusion4p D Lv

end Formalism.L2.GlobalTheoryTheory.GenusMassVolumes

end
