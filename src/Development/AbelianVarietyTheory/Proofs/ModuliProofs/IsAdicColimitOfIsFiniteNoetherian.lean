import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FiniteTorsLift

open GlobalTheory.TorusModel GlobalTheory.FormalPoint GlobalTheory.AdicColimit GlobalTheory.TorsionFormCompare

theorem isAdicColimit_of_isFinite_noetherian {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    (hc : IsAdicComplete (maximalIdeal R) R) (N : Over (Sp R)) [IsFinite N.hom] :
    IsAdicColimit (maximalIdeal R) N := by
  have : IsAffine N.left := isAffine_of_isAffineHom N.hom
  obtain ⟨φ, hφ⟩ := Spec.map_surjective (N.left.isoSpec.inv ≫ N.hom)
  have hf : IsFinite (Spec.map φ) := by rw [hφ]; infer_instance
  rw [IsFinite.SpecMap_iff] at hf
  letI : Algebra R Γ(N.left, ⊤) := φ.hom.toAlgebra
  have : Module.Finite R Γ(N.left, ⊤) := hf
  have : HenselianLocalRing R :=
    { is_henselian := fun f hf a₀ h₁ h₂ =>
        HenselianRing.is_henselian (I := maximalIdeal R) f hf a₀ h₁ (h₂.map _) }
  have H := isAdicColimit_finite_henselian_of_local isAdicColimit_spec_of_isLocalRing
    isAdicColimit_of_disjoint_cover R (maximalIdeal R) R Γ(N.left, ⊤) (algebraMap R _)
    (ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.isAdicComplete_finite_algebra _)
  exact IsAdicColimit.of_iso (Over.isoMk N.left.isoSpec.symm hφ.symm) H

end GlobalTheory.FiniteTorsLift
