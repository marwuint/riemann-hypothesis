import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVHom
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.GlobFnsDvr
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PullCub
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ExtVCat

set_option autoImplicit false

noncomputable section

namespace ReciprocityTheory.ChartRestriction.G.Geo.Tor

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out
open scoped CategoryTheory.Obj

theorem specMap_appTop_injective {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (hf : Function.Injective f) :
    Function.Injective (Spec.map (CommRingCat.ofHom f)).appTop.hom := by
  intro a b hab
  have n := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom f)
  have ha := congrArg (fun g => g.hom a) n
  have hb := congrArg (fun g => g.hom b) n
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at ha hb
  rw [hab, hb] at ha
  have h2 := hf ha
  have i := (Scheme.ΓSpecIso (CommRingCat.of R)).hom_inv_id
  have ia := congrArg (fun g => g.hom a) i
  have ib := congrArg (fun g => g.hom b) i
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at ia ib
  rw [← ia, ← ib, h2]

end ReciprocityTheory.ChartRestriction.G.Geo.Tor
