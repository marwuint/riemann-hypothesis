import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs

noncomputable section

open Matrix Module
open scoped ContDiff

namespace PositivityTheory.RgBcC.VC.GFB

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def lmul (a b : Mat n) : Mat n →L[ℝ] Mat n :=
  LinearMap.toContinuousLinearMap
    { toFun := fun y => a * y * b
      map_add' := fun y z => by simp [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c y => by simp [Matrix.mul_smul, Matrix.smul_mul] }

theorem lmul_apply (a b y : Mat n) : lmul a b y = a * y * b := rfl

end PositivityTheory.RgBcC.VC.GFB
