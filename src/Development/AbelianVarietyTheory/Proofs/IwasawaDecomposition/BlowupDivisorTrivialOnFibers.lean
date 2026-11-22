import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory

theorem cechPic_sp_field_eq_zero (K : Type) [Field K] (c : GlobalTheory.CechPic.Pic (Sp K)) : c = 0 := by
  obtain ⟨L, hL, rfl⟩ := GlobalTheory.CechPic.cls_surj c
  exact (GlobalTheory.CechPic.cls_eq_zero_iff hL).2 (GlobalTheory.LB.exists_isGen_of_isLocalRing hL)

end GlobalTheory
