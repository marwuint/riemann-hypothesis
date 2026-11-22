import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PtAlgSpOver
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeFiltrationsOrthogonalLineBundlePairingProdu
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairingIsPerfectAbelianSchemesBothKernelsZero
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open ReciprocityTheory.ChartRestriction.G.Geo.Tor (Sp spMap epsR IsTangent IsGrpPullback)
open ReciprocityTheory.ChartRestriction.G.Semi (IsAbelianScheme LB)
open GlobalTheory GlobalTheory.CatCoh GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.PDiv GlobalTheory.PtExt
attribute [local instance] Over.cartesianMonoidalCategory

theorem GlobalTheory.PtExt.perfect_and_orthogonal : GlobalTheory.Published.AbelianHodgeDeRham → ∀ (R : Type) [CommRing R] (A B : Over (Sp R)) [GrpObj A] [GrpObj B] (g : ℕ), IsAbelianScheme A → IsAbelianScheme B → SmoothOfRelativeDimension g A.hom → SmoothOfRelativeDimension g B.hom → ∀ P : LB (A ⊗ B).left, AbDual.IsPerfect A B P → ∀ φ : HdR A →ₗ[R] HdR B →ₗ[R] R, AbDual.IsCorrForm (dp0 R) (𝟙 _) A B P φ → φ.IsPerfPair ∧ ∀ x ∈ Fil A, ∀ y ∈ Fil B, φ x y = 0 := by
  intro hHdR R _ A B _ _ g hA hB hgA hgB P hP φ hφ
  exact ⟨_root_.GlobalTheory.AbDual.isPerfPair_of_abelianHodgeDeRham hHdR R A B g hA hB hgA hgB P hP φ hφ,
    _root_.GlobalTheory.PtExt.HodgeOrth.fil_orthogonal hHdR R A B g hA hB hgA hgB P hP.isLB φ hφ⟩
