import Mathlib
import GroundTheory.GlobalFields.LocalAtPlace
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.IsHermitianForExH

set_option linter.unusedSectionVars false

noncomputable section

namespace GroundTheory.Heights₂.Theta

namespace SwmCone

open MeasureTheory Topology Filter Matrix TensorProduct NumberField IsDedekindDomain
  GroundTheory.Automorphic GroundTheory.Heights₂.Theta.IsoFrames
open scoped ENNReal NNReal

attribute [local instance] IsoFrames.scTop

section Local

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {n : ℕ}

variable (K E R) in

def cTr {m l : Type*} (g : Matrix m l (R ⊗[K] E)) : Matrix l m (R ⊗[K] E) :=
  (g.map (conjBase K E R))ᵀ

def frameMul (X : FrameSp K E R ι n) (g : Matrix (Fin n) (Fin n) (R ⊗[K] E)) :
    FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from (show Matrix ι (Fin n) (R ⊗[K] E) from X) * g

def frameSMul (h : Matrix ι ι (R ⊗[K] E)) (X : FrameSp K E R ι n) : FrameSp K E R ι n :=
  show Matrix ι (Fin n) (R ⊗[K] E) from h * (show Matrix ι (Fin n) (R ⊗[K] E) from X)

variable [IsTopologicalRing R] [LocallyCompactSpace R]

end Local

end SwmCone

end GroundTheory.Heights₂.Theta
