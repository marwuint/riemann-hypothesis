import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HomogeneousLocalization
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace NumberField GroundTheory.Arith.SchemeCoh
open scoped LinearAlgebra.Projectivization

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

noncomputable section

namespace SectionsLatticeFS

open ProjScheme

def FSCoord.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (P : MvPolynomial (Fin (N + 1)) A)
    (hP : P ∈ ProjSpace.grading A N n) (x : (self A N).complexPoints ρ) (j : Fin (N + 1))
    (hj : x.1.rep j ≠ 0),
      fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
          (isBasisOn_frame (A := A) j n) ((self A N).evalGlobalSection (twistN A N n) x (polySection hP)) *
        x.1.rep j ^ n = evalAt ρ x.1.rep P

def FSIndex.Statement : Prop :=
  ∀ (A : Type u) [CommRing A] (N n : ℕ) (ρ : A →+* ℂ) (x : (self A N).complexPoints ρ)
    (j : Fin (N + 1)) (hj : x.1.rep j ≠ 0) (s : (self A N).Fibre (twistN A N n) x),
      fsFibreNorm n ρ x s =
        ‖fibreEquivComplex ((self A N).evalAtPoint x) (point_mem_stdOpen x hj)
            (isBasisOn_frame (A := A) j n) s‖ * ‖x.1.rep j‖ ^ n / norm2 x.1.rep ^ n

end SectionsLatticeFS

end

end GroundTheory.Heights₂.Heights
