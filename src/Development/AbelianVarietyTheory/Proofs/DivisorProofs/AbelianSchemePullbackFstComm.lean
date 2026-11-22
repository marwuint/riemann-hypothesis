import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PoincareDeRhamDuality
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ZeroSectionBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheaf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDeRhamSheafIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUniqueTangentOfValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TanEvBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAbelianSchemeOnAff

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry Limits TopologicalSpace MonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.DeRham GlobalTheory.DeRhamSheaf GlobalTheory.LieVB
open GlobalTheory.Conormal GlobalTheory.Cris GlobalTheory.TanFibre
open GlobalTheory.Twist (resM app_resM)
open GlobalTheory.QCoh (pullbackSections)
open GlobalTheory.DualPull (appLE_resG resG_appLE)
open ReciprocityTheory.ChartRestriction.G.Pdiv (specO ptMap dualScale)
open GlobalTheory.LocM (spMap_dualMap_comp spMap_dualMap_epsFn)
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.HodgeSub.Nat

section Form

variable {k k' : Type} [CommRing k] [CommRing k'] {X Y : Scheme.{0}} {π : Y ⟶ X} {e : X ⟶ Y}

variable {A : Over X} [GrpObj A] {x : Sp k ⟶ X} {G : Over (Sp k)} [GrpObj G] {ψ : G.left ⟶ A.left}

theorem epsZero_comp_of_isTangent {y : epsR k ⟶ G} (hy : IsTangent y) : epsZero k ≫ y = η :=
  Over.OverMorphism.ext hy

def ev (σ : Γ(omega G, ⊤)) : (conormal (unitSec G) ⟶ conormal (sec (epsZero k))) →+ k :=
  AddMonoidHom.mk' (fun α => (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app ⊤ (α.app ⊤ σ))) fun α β =>
    (congrArg (Scheme.ΓSpecIso (.of k)).hom (map_add ((epsIso k).hom.app ⊤).hom (α.app ⊤ σ) (β.app ⊤ σ))).trans
      (map_add _ _ _)

def tv (σ : Γ(omega G, ⊤)) (v : epsR k ⟶ G) (hv : IsTangent v) : k :=
  ev σ (cotMap (T' := specO k (DualNumber k)) v (epsZero_comp_of_isTangent hv))

theorem tv_scale (σ : Γ(omega G, ⊤)) (r : k) {y : epsR k ⟶ G} (hy : IsTangent y)
    (hz : IsTangent (GrpTangent.epsScale r ≫ y)) : tv σ _ hz = r * tv σ y hy := by
  have e := cotMap_comp (T' := specO k (DualNumber k)) (epsZero_comp_of_isTangent hy) (epsZero_dualScale r)
    (χ := GrpTangent.epsScale r ≫ y) rfl (epsZero_comp_of_isTangent hz)
  rw [cotMap_dualScale] at e
  refine (congrArg (ev σ) e).symm.trans ?_
  refine (congrArg (Scheme.ΓSpecIso (.of k)).hom ((epsIso k).hom.app_smul (cst k r)
    ((cotMap (T' := specO k (DualNumber k)) y (epsZero_comp_of_isTangent hy)).app ⊤ σ))).trans ?_
  refine (map_mul _ _ _).trans ?_
  rw [Iso.inv_hom_id_apply]
  rfl

theorem tv_mul [QuasiSeparated G.hom] (σ : Γ(omega G, ⊤)) {y z : epsR k ⟶ G} (hy : IsTangent y)
    (hz : IsTangent z) (h : IsTangent (y * z)) : tv σ _ h = tv σ y hy + tv σ z hz :=
  (congrArg (ev σ) (cotMap_mul (T := specO k (DualNumber k)) (epsZero_comp_of_isTangent hy)
    (epsZero_comp_of_isTangent hz) (epsZero_comp_of_isTangent h))).trans (map_add _ _ _)

theorem tv_one (σ : Γ(omega G, ⊤)) (h : IsTangent (1 : epsR k ⟶ G)) : tv σ _ h = 0 :=
  (congrArg (ev σ) (cotMap_eq_zero (T' := specO k (DualNumber k)) (Hom.one_def).symm
    (epsZero_comp_of_isTangent h))).trans (map_zero _)

def Good (σ : Γ(omega G, ⊤)) (c : primDR G) (h : HdR G) : Prop :=
  ∀ (v : epsR k ⟶ G) (hv : IsLieImage h v), h c = tv σ v hv.1

variable {σ : Γ(omega G, ⊤)} {c : primDR G}

theorem Good.add [QuasiSeparated G.hom] (H : LieExact G) {a b : HdR G} (ha : Good σ c a) (hb : Good σ c b) :
    Good σ c (a + b) := fun v hv ↦ by
  obtain ⟨va, ea, -⟩ := H.1 a
  obtain ⟨vb, eb, -⟩ := H.1 b
  obtain rfl := (H.1 _).unique hv (ea.add eb)
  rw [tv_mul σ ea.1 eb.1, ← ha _ ea, ← hb _ eb, LinearMap.add_apply]

theorem Good.zero (H : LieExact G) : Good σ c 0 := fun v hv ↦ by
  obtain rfl := (H.1 _).unique hv (isLieImage_one_iff.2 (zero_mem _))
  rw [tv_one, LinearMap.zero_apply]

theorem Good.smul (H : LieExact G) (r : k) {a : HdR G} (ha : Good σ c a) : Good σ c (r • a) := fun v hv ↦ by
  obtain ⟨va, ea, -⟩ := H.1 a
  obtain rfl := (H.1 _).unique hv (ea.smul r)
  rw [tv_scale σ r ea.1, ← ha _ ea, LinearMap.smul_apply, smul_eq_mul]

end Form

end GlobalTheory.HodgeSub.Nat
