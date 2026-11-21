import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsRegularRingOfSmooth
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Definitions.Divisors.SmoothOfRelativeDimensionPspace
import ReciprocityTheory.AnalyticForms.RegularLocalRings.WChartsC

noncomputable section

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

namespace GlobalTheory.Principalise.Model

attribute [local instance] MvPolynomial.gradedAlgebra

section Proj
variable (k : Type) [Field k] (N : ℕ)

def hypPt : PSpace k (N + 1) :=
  (⟨⟨Ideal.span {MvPolynomial.X 0}, Ideal.homogeneous_span _ _ (by
      rintro _ rfl; exact ⟨1, MvPolynomial.isHomogeneous_X k 0⟩)⟩,
    (Ideal.span_singleton_prime (MvPolynomial.X_ne_zero 0)).2 MvPolynomial.X_prime, fun h => by
      have h1 : (MvPolynomial.X 1 : MvPolynomial (Fin (N + 1 + 1)) k) ∈
          HomogeneousIdeal.irrelevant (MvPolynomial.homogeneousSubmodule (Fin (N + 1 + 1)) k) :=
        HomogeneousIdeal.mem_irrelevant_of_mem _ (i := 1) one_pos (MvPolynomial.isHomogeneous_X k 1)
      have h2 := Ideal.mem_span_singleton.1 (h h1)
      rw [MvPolynomial.X_dvd_X] at h2
      exact absurd h2 (by simp)⟩ : ProjectiveSpectrum _)

def hypIdeal : (PSpace k (N + 1)).IdealSheafData :=
  Scheme.IdealSheafData.vanishingIdeal (Opens.compl (Proj.basicOpen _ (MvPolynomial.X 0)))

theorem mem_support : hypPt k N ∈ (hypIdeal k N).support := by
  rw [hypIdeal, ← SetLike.mem_coe, Scheme.IdealSheafData.coe_support_vanishingIdeal]
  exact fun h => (Proj.mem_basicOpen _ _ _).1 h (Ideal.mem_span_singleton_self _)

end Proj

section Line
variable (k : Type) [Field k]

abbrev origin : Sp k ⟶ Sp (Polynomial k) := spMap (Polynomial.evalRingHom 0)

instance : IsClosedImmersion (origin k) :=
  IsClosedImmersion.spec_of_surjective _ fun a => ⟨Polynomial.C a, by simp⟩

end Line

end GlobalTheory.Principalise.Model
