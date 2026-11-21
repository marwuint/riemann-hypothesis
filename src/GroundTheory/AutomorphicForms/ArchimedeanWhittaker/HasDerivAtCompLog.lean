import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.Density

namespace GroundTheory.Automorphic.ArchWhittaker

open Matrix NormedSpace Complex MeasureTheory Filter Topology Set
open scoped Matrix.Norms.L2Operator Real InnerProductSpace ContDiff

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (σ : UnitaryRep FiltrationCocycleLiftCriterion H)

noncomputable abbrev πσ : BanachRep FiltrationCocycleLiftCriterion H := BanachRep.ofUnitary σ

abbrev IsSm (v : H) : Prop := hGL2.IsSmoothVector (πσ σ) v

variable (l : hGL2.smoothVectors (πσ σ) →ₗ[ℂ] ℂ)

open Classical in

noncomputable def lT (x : H) : ℂ := if hx : IsSm σ x then l ⟨x, hx⟩ else 0

variable {σ l}

variable (σ l)

variable {σ l}

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker

namespace GroundTheory.Automorphic.ArchWhittaker

end GroundTheory.Automorphic.ArchWhittaker
