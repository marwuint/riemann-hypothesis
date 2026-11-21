import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TateProductRigidificationTrivial
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Divisors.EvenDefect
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyIsPullDegCompOfInjective
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.IsPullFOfGenRel
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsIsPullDegOfVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ValEqOfAppInjective

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.Mum

noncomputable section

namespace GlobalTheory.RescaleLift

open GlobalTheory.ArcPull GlobalTheory.ArcQ
open GlobalTheory.PsiEvenPull (proj)

theorem isUnit_of_basicOpen_top {Y : Scheme.{0}} (s : Γ(Y, ⊤)) (h : Y.basicOpen s = ⊤) : IsUnit s :=
  Y.toRingedSpace.isUnit_of_isUnit_germ _ _ fun x hx => (Y.mem_basicOpen _ x hx).1 (h.ge hx)

abbrev fnSp (A : Type) [CommRing A] : A →+* Γ(Sp A, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom

theorem appTop_comp_spMap {R₀ A : Type} [CommRing R₀] [CommRing A] (α : R₀ →+* A) {Z : Scheme.{0}}
    (s : Z ⟶ Sp A) (r : R₀) : (s ≫ spMap α).appTop.hom (fnSp R₀ r) = s.appTop.hom (fnSp A (α r)) := by
  have nat := congrArg (fun q => q.hom r) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom α))
  rw [Scheme.Hom.comp_appTop]
  exact congrArg s.appTop.hom nat.symm

def fnOn {R₀ : Type} [CommRing R₀] (W : (Sp R₀).Opens) : R₀ →+* Γ(W.toScheme, ⊤) :=
  W.ι.appTop.hom.comp (fnSp R₀)

theorem appTop_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) :
    t.appTop.hom (fnOn W r) = s.appTop.hom (fnSp A (α r)) := by
  have e : t.appTop.hom (fnOn W r) = (t ≫ W.ι).appTop.hom (fnSp R₀ r) := by
    rw [Scheme.Hom.comp_appTop]; rfl
  rw [e, h, appTop_comp_spMap]

theorem gm_fnOn {R₀ A : Type} [CommRing R₀] [CommRing A] (W : (Sp R₀).Opens) (α : R₀ →+* A) {Z : Scheme.{0}}
    (t : Z ⟶ W.toScheme) (s : Z ⟶ Sp A) (h : t ≫ W.ι = s ≫ spMap α) (r : R₀) (u : Γ(W.toScheme, ⊤)ˣ) (v : Aˣ)
    (hu : (u : Γ(W.toScheme, ⊤)) = fnOn W r) (hv : (v : A) = α r) (z : Z) :
    gm t z ⊤ u = gm s z ⊤ (unitOn v) := by
  rw [GlobalTheory.UU.gm_top t, GlobalTheory.UU.gm_top s]
  congr 1
  apply Units.ext
  show t.appTop.hom (u : Γ(W.toScheme, ⊤)) = s.appTop.hom (fnSp A (v : A))
  rw [hu, hv, appTop_fnOn W α t s h r]

theorem isUnit_fnOn {R₀ : Type} [CommRing R₀] (f r : R₀) (N : ℕ) (hr : r ∣ f ^ N) :
    IsUnit (fnOn ((Sp R₀).basicOpen (fnSp R₀ f)) r) := by
  set W := (Sp R₀).basicOpen (fnSp R₀ f)
  have hf : IsUnit (fnOn W f) := isUnit_of_basicOpen_top _ (by
    have e := Scheme.preimage_basicOpen W.ι (fnSp R₀ f)
    rw [Scheme.Opens.ι_preimage_self] at e
    exact e.symm)
  exact isUnit_of_dvd_unit (map_dvd (fnOn W) hr |>.trans (by rw [map_pow])) (hf.pow N)

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

end GlobalTheory.RescaleLift

namespace GlobalTheory.RescaleLift

end GlobalTheory.RescaleLift
