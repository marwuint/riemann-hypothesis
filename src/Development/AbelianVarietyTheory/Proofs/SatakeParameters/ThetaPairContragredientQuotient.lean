import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsParahoricVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EventuallyCompSideMulEq
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL
open scoped TensorProduct

namespace GlobalTheory.ThetaGL.DualPair

section General

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def ev (V : Type) [AddCommGroup V] [Module ℂ V] (π : Representation ℂ G W) :
    V ⊗[ℂ] smoothPart π.dual →ₗ[ℂ] W →ₗ[ℂ] V :=
  TensorProduct.lift (LinearMap.mk₂ ℂ
    (fun (v : V) (l : smoothPart π.dual) => (l : Module.Dual ℂ W).smulRight v)
    (fun v v' l => by ext w; simp)
    (fun c v l => by
      ext w
      show (l : Module.Dual ℂ W) w • c • v = c • (l : Module.Dual ℂ W) w • v
      exact smul_comm _ _ _)
    (fun v l l' => by ext w; simp [add_smul])
    (fun c v l => by ext w; simp [smul_smul]))

@[simp] theorem ev_tmul (π : Representation ℂ G W) (v : V) (l : smoothPart π.dual) (w : W) :
    ev V π (v ⊗ₜ l) w = (l : Module.Dual ℂ W) w • v := rfl

end General

end GlobalTheory.ThetaGL.DualPair

