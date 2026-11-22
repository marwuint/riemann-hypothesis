import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HodgeTateLatticePointFinrankTateModule
import Development.AbelianVarietyTheory.Definitions.Divisors.TorsionTowersOfDivisibleGroup
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsIsPullbackBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuasiCompactZeroSec
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIsoToBidualOfLocalFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSqZeroNaturality
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SqZeroPointEqOfCotangentFormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteProjectiveCotangentGlobalSectionsGroupSche
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCotangentFrameSmoothGroupScheme
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TangentPhiInjectiveCriterion
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.NonemptyTorusExtensionOfIsGt
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.TorusExtensionPointsDivisible
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.MapDegreeEqExpCharPowMulCardKernel
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow

set_option autoImplicit false

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.ZV GlobalTheory.DegKer
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.SemiAbelianTower

theorem finrank_eq_of_mapDeg {X Y : Scheme.{0}} [IsIntegral Y] (φ : X ⟶ Y) [IsFinite φ] [Flat φ] {D : ℕ}
    (hD : MapDeg φ D) (y : Y) : φ.finrank y = D := by
  obtain ⟨_, ⟨U, hU, rfl⟩, hy, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  replace hU : IsAffineOpen U := hU
  haveI : Nonempty U := ⟨⟨_, hy⟩⟩
  letI := (φ.app U).hom.toAlgebra
  haveI : Module.Finite Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := φ.finite_app U hU
  haveI : Module.Flat Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) := by
    have := φ.flat_appLE hU (hU.preimage φ) le_rfl
    rwa [Scheme.Hom.appLE_eq_app] at this
  have hp : IsPullback (hU.preimage φ).fromSpec (Spec.map (φ.app U)) φ hU.fromSpec :=
    (IsOpenImmersion.isPullback _ _ _ _ (by
      rw [Scheme.Hom.app_eq_appLE, IsAffineOpen.SpecMap_appLE_fromSpec φ hU (hU.preimage φ)])
      (by simp)).flip
  obtain ⟨q, rfl⟩ : y ∈ Set.range hU.fromSpec := by rw [hU.range_fromSpec]; exact hy
  rw [← hD.finrank_eq U hU ⟨_, hy⟩, ← FiniteCover.rankAtStalk_bot,
    Module.rankAtStalk_eq_of_le_of_finite_of_flat _ (p := ⊥) (q := q) bot_le,
    ← Scheme.Hom.finrank_of_isPullback _ _ _ _ hp q]
  exact Scheme.Hom.finrank_SpecMap_algebraMap Γ(Y, U) Γ(X, φ ⁻¹ᵁ U) _

end GlobalTheory.SemiAbelianTower
