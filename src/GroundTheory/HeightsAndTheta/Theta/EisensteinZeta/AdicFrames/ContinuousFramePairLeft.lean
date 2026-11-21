import Mathlib
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.FramePairAddRight
import GroundTheory.HeightsAndTheta.Theta.EisensteinZeta.AdicFrames.InstSecondCountableTopologyFrameSp

set_option linter.unusedSectionVars false

namespace GroundTheory.Heights₂.Theta

namespace IsoFrames

namespace Chart

open MeasureTheory Topology Filter Set Matrix TensorProduct GroundTheory.Automorphic

noncomputable section

variable {K E : Type*} [Field K] [Field E] [Algebra K E] [Algebra.IsQuadraticExtension K E]
variable {R : Type*} [CommRing R] [Algebra K R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R] [SecondCountableTopology R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {p : ℕ} {H : Matrix ι ι E}

attribute [local instance] scTop finite_of_isQuadraticExtension isModuleTopology_tensor
  isTopologicalRing_tensor

local infixl:70 " ⬝ " => @HMul.hMul _ _ _ instHMulOfFintypeOfMulOfAddCommMonoid

def toM {κ : Type*} [Fintype κ] [DecidableEq κ] (X : FrameSp K E R κ p) : Matrix κ (Fin p) (R ⊗[K] E) := X

def ofM {κ : Type*} [Fintype κ] [DecidableEq κ] (M : Matrix κ (Fin p) (R ⊗[K] E)) : FrameSp K E R κ p := M

variable (R p) in

def gramH (hH : IsHermitianFor (conjHom K E) H) (X : FrameSp K E R ι p) : HermSp K E R p :=
  ⟨gram K E R H (toM X), cT_framePair hH _ _⟩

variable (R p H) in

def chartSet (Z : Matrix ι (Fin p) (R ⊗[K] E)) : Set (FrameSp K E R ι p) :=
  {X | IsUnit (framePair K E R H Z (toM X)).det}

variable (H) in

def chartShift (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) :
    FrameSp K E R ι p → FrameSp K E R (Fin p) p := by
  classical exact (chartSet R p H Z).piecewise (fun X ↦ ofM (shiftT (H := H) Z (toM X) S.mat)) 0

variable (H) in

def chartAct (Z : Matrix ι (Fin p) (R ⊗[K] E)) (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    FrameSp K E R ι p :=
  ofM (toM X + Z ⬝ toM (chartShift H Z S X))

variable {Z : Matrix ι (Fin p) (R ⊗[K] E)}

theorem toM_chartAct (S : HermSp K E R p) (X : FrameSp K E R ι p) :
    toM (chartAct H Z S X) = toM X + Z ⬝ toM (chartShift H Z S X) := rfl

variable (hRu : IsOpen {r : R | IsUnit r}) (hRi : ∀ r : R, IsUnit r → ContinuousAt Ring.inverse r)

end

end Chart

end IsoFrames

end GroundTheory.Heights₂.Theta
