import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.HasDerivAtCompLog

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

def IsWhit (σ : UnitaryRep FiltrationCocycleLiftCriterion H) (ψ : ℝ → ℂ) (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ) : Prop :=
  ∀ (x : ℝ) (w : H), IsSm σ w → lT σ l (σ (nMat x) w) = ψ x * lT σ l w

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep FiltrationCocycleLiftCriterion H}

noncomputable def toLin (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ where
  toFun w := l w
  map_add' a b := l.map_add a b
  map_smul' c a := l.map_smul c a

theorem toLin_apply (l : hGL2.SmoothFrechet (πσ σ) →L[ℂ] ℂ) (w : hGL2.smoothVectors (πσ σ)) :
    toLin l w = l w := rfl

end GroundTheory.Automorphic.ArchWhittaker
