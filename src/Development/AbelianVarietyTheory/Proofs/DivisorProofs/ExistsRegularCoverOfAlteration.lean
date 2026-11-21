import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SecondChernDegreeVanishesTrueSurfaces

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.RegCoverExists

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in
private theorem isSeparated_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R') :
    IsSeparated (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c) := by
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R) := by
    show IsAffine (Spec (CommRingCat.of R)); infer_instance
  have : IsAffine (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R') := by
    show IsAffine (Spec (CommRingCat.of R')); infer_instance
  infer_instance

set_option autoImplicit false in
open CategoryTheory AlgebraicGeometry in

theorem _root_.GlobalTheory.RegCoverExists.isProjOver_of_comp_spMap {R R' : Type} [CommRing R] [CommRing R'] (c : R →+* R')
    {Y : Scheme.{0}} {f : Y ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R'} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver (f ≫ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap c)) : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsProjOver f := by
  obtain ⟨N, i, hi, hif⟩ := h
  have hP := _root_.GlobalTheory.ProjSpace.isPullback_baseChange N c
  haveI := isSeparated_spMap c
  haveI : IsSeparated (_root_.GlobalTheory.ProjSpace.baseChange N c) :=
    MorphismProperty.of_isPullback (P := @IsSeparated) hP.flip inferInstance
  refine ⟨N, hP.lift i f hif, ?_, hP.lift_snd _ _ _⟩
  haveI : IsClosedImmersion (hP.lift i f hif ≫ _root_.GlobalTheory.ProjSpace.baseChange N c) := by
    rw [hP.lift_fst]; exact hi
  exact IsClosedImmersion.of_comp _ (_root_.GlobalTheory.ProjSpace.baseChange N c)

end GlobalTheory.RegCoverExists

end
