import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM
open scoped CategoryTheory.Obj

namespace GlobalTheory.ZM.ProjExt

theorem eq_pt_of_secCoord {o : Type} [CommRing o] {m : ℕ} {A : Type} [CommRing A] (c : o →+* A)
    (y : Sp A ⟶ PSpace o m) (hy : y ≫ PSpace.str o m = spMap c) (v : Fin (m + 1) → A)
    (h : SecCoord (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) y v) :
    ∃ hv : Ideal.span (Set.range v) = ⊤, y = GlobalTheory.ProjSpace.pt c v hv := by
  have h1 := (RepBC.secCoord_pull (GlobalTheory.ProjSpace.O1 o m) (GlobalTheory.ProjSpace.coord o m) (𝟙 _) y v).2
    (by rwa [Category.comp_id])
  obtain ⟨hv, e⟩ := (ProjCoord.secCoord_iff (Equiv.refl _) (𝟙 _) c y (by rwa [Category.comp_id]) v).1 h1
  exact ⟨hv, (Category.comp_id _).symm.trans e⟩

end GlobalTheory.ZM.ProjExt
