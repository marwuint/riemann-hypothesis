import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IrrelevantLeMapScaleGraded
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.HomDerivativeClosure
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.IsAbelianSchemeSchemeOver

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.WeierstrassCurve GlobalTheory.AddLaw GlobalTheory.WeightScale

noncomputable section

namespace GlobalTheory.CMCurve

variable {R : Type} [CommRing R]

variable (R) in

def gaussianCurve : WeierstrassCurve R := ⟨0, 0, 0, -1, 0⟩

section Gaussian

variable {i : R} (hi : i ^ 2 = -1)
include hi

theorem neg_mul_self_eq_one : -i * i = 1 := by linear_combination -hi

theorem curve_gaussianCurve : curve (-i) (gaussianCurve R) = gaussianCurve R := by
  ext <;> simp only [curve, gaussianCurve, mul_zero]
  linear_combination (1 - i ^ 2) * hi

def gaussianAut : schemeOver (gaussianCurve R) ⟶ schemeOver (gaussianCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (neg_mul_self_eq_one hi)) (curve_gaussianCurve hi)

variable [(gaussianCurve R).IsElliptic]

instance isMonHom_gaussianAut : IsMonHom (gaussianAut hi) := isMonHom_scaleOver ..

end Gaussian

variable (R) in

def eisensteinCurve : WeierstrassCurve R := ⟨0, 0, 1, 0, 0⟩

section Eisenstein

variable {w : R} (hw : w ^ 2 + w + 1 = 0)
include hw

theorem sq_mul_self_eq_one : w ^ 2 * w = 1 := by linear_combination (w - 1) * hw

theorem curve_eisensteinCurve : curve (w ^ 2) (eisensteinCurve R) = eisensteinCurve R := by
  ext <;> simp only [curve, eisensteinCurve, mul_zero]
  linear_combination (w ^ 3 + 1) * sq_mul_self_eq_one hw

def eisensteinAut : schemeOver (eisensteinCurve R) ⟶ schemeOver (eisensteinCurve R) :=
  scaleOver _ (IsUnit.of_mul_eq_one _ (sq_mul_self_eq_one hw)) (curve_eisensteinCurve hw)

variable [(eisensteinCurve R).IsElliptic]

instance isMonHom_eisensteinAut : IsMonHom (eisensteinAut hw) := isMonHom_scaleOver ..

end Eisenstein

end GlobalTheory.CMCurve
