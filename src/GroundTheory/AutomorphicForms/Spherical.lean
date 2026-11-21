import Mathlib
import GroundTheory.AutomorphicForms.SphericalIntegral

noncomputable section

namespace GroundTheory.Automorphic

open MeasureTheory GLnLocal Iwasawa Parabolic HeckeAlgebra HeckeAlgebraLevel

namespace Spherical

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

section Characters

variable [MeasurableSpace (GL (Fin n) F)] [BorelSpace (GL (Fin n) F)]
  {μ : Measure (GL (Fin n) F)} [μ.IsHaarMeasure]

theorem exists_ker_sphericalCharacter_eq (I : Ideal (SphericalHecke μ (F := F) (n := n)))
    [I.IsMaximal] : ∃ w : Fin n → ℂˣ,
      RingHom.ker (sphericalCharacter μ (isUnramified_unramifiedChar (F := F) w)) = I := by
  haveI := isIntegral_satake (μ := μ) (F := F) (n := n)
  obtain ⟨w, hw⟩ := exists_ker_evalAt_comp_eq (satakeHom μ) satakeHom_injective I
  exact ⟨w, by rw [← evalAt_comp_satakeHom]; exact hw⟩

end Characters

end Spherical

end GroundTheory.Automorphic
