import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AffineOpenChartCompStructureEqSpMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueLiftSpecOfIsLocalizationAway
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsLeftInverseOfFibrewiseInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsCompletedStrictHens
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IsProjOverCompOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsDomainAndIsIntegrallyClosedAtPrimeOfSmoothOfCo
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsFiniteNormalFlatClosure
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PointsOfClosureInProjectiveSpace

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DRFlag GlobalTheory.ProjSpace
open GlobalTheory.FlagMod (ev ev_spMap le_preimage_comp)

namespace GlobalTheory.SubClosure

section General

variable {O S S' : Type} [CommRing O] [CommRing S] [CommRing S'] {N : ℕ}

def IsPt (q : Sp S ⟶ PSpace O N) (v : Fin (N + 1) → S) : Prop := ∃ (g : O →+* S) (hv : _), q = pt g v hv

theorem IsPt.smul {q : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) (u : Sˣ) : IsPt q (u • v) := by
  obtain ⟨g, hv, rfl⟩ := h
  exact ⟨g, _, (pt_units_smul g hv u).symm⟩

theorem IsPt.exists_eq {q : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) {g : O →+* S}
    (e : q ≫ PSpace.str O N = ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap g) : ∃ hv, q = pt g v hv := by
  obtain ⟨g', hv, rfl⟩ := h
  rw [pt_str] at e
  obtain rfl : g' = g := congrArg CommRingCat.Hom.hom (Spec.map_injective e)
  exact ⟨hv, rfl⟩

theorem IsPt.eq {q q' : Sp S ⟶ PSpace O N} {v : Fin (N + 1) → S} (h : IsPt q v) (h' : IsPt q' v)
    (e : q ≫ PSpace.str O N = q' ≫ PSpace.str O N) : q = q' := by
  obtain ⟨g, hv, rfl⟩ := h'
  rw [pt_str] at e
  exact (h.exists_eq e).2

theorem IsPt.ne_zero {K : Type} [Field K] {q : Sp K ⟶ PSpace O N} {v : Fin (N + 1) → K} (h : IsPt q v) : v ≠ 0 := by
  obtain ⟨g, hv, -⟩ := h
  exact span_range_eq_top_iff_ne_zero.1 hv

instance subsingleton_sp (K : Type) [Field K] : Subsingleton (Sp K) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum K))

end General

end GlobalTheory.SubClosure
