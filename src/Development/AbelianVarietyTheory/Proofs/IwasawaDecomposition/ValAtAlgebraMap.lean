import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo Formalism.BasicNotions

namespace GlobalTheory.TrueGeo.OfModel

section Values

variable {K : Type} [Field K] {Z : Scheme.{0}} [IsIntegral Z] (y : Sp K ⟶ Z)

theorem valAt_algebraMap (a : Z.presheaf.stalk (below y)) :
    valAt y (algebraMap _ Z.functionField a) = (Scheme.stalkClosedPointTo y).hom a := by
  have h : RegAt (below y) (algebraMap _ Z.functionField a) := ⟨a, rfl⟩
  rw [valAt, dif_pos h]
  exact congrArg _ (IsFractionRing.injective (Z.presheaf.stalk (below y)) Z.functionField h.choose_spec)

theorem valAt_mul {f g : Z.functionField} (hf : RegAt (below y) f) (hg : RegAt (below y) g) :
    valAt y (f * g) = valAt y f * valAt y g := by
  obtain ⟨a, rfl⟩ := hf
  obtain ⟨b, rfl⟩ := hg
  rw [← map_mul, valAt_algebraMap, valAt_algebraMap, valAt_algebraMap, map_mul]

theorem valAt_fnOf {U : Z.Opens} (hU : below y ∈ U) (h : ⊤ ≤ y ⁻¹ᵁ U) (a : Γ(Z, U)) :
    valAt y (fnOf U (gen_mem hU) a) =
      (y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom a := by
  have e : Z.presheaf.germ U _ hU ≫ Scheme.stalkClosedPointTo (R := CommRingCat.of K) y =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom := by
    rw [Scheme.germ_stalkClosedPointTo]
    simp [Iso.trans_hom, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map_assoc]
  rw [← algebraMap_germ hU, valAt_algebraMap, ← e]
  rfl

end Values

theorem eval_pull {K O : Type} [CommRing K] [CommRing O] (φ : O →+* K) {X Z : Scheme.{0}} (j : Z ⟶ X)
    (y : Sp K ⟶ Z) (yt : Sp O ⟶ X) (e : spMap φ ≫ yt = y ≫ j) {U : X.Opens} {W : Z.Opens}
    (hW : W ≤ j ⁻¹ᵁ U) (h : ⊤ ≤ y ⁻¹ᵁ W) (ht : ⊤ ≤ yt ⁻¹ᵁ U) (a : Γ(X, U)) :
    (y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom).hom ((j.appLE U W hW).hom a) =
      φ ((yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom).hom a) := by
  have e1 : j.appLE U W hW ≫ y.appLE W ⊤ h = yt.appLE U ⊤ ht ≫ (spMap φ).appTop := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_comp_appLE]
    refine Eq.trans ?_ (Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _).symm
    simp only [e]
  have e2 := Scheme.ΓSpecIso_naturality (CommRingCat.ofHom φ)
  have e3 : j.appLE U W hW ≫ y.appLE W ⊤ h ≫ (Scheme.ΓSpecIso (CommRingCat.of K)).hom =
      (yt.appLE U ⊤ ht ≫ (Scheme.ΓSpecIso (CommRingCat.of O)).hom) ≫ CommRingCat.ofHom φ := by
    rw [← Category.assoc, e1, Category.assoc, e2, Category.assoc]
  exact congrArg (fun ψ => ψ.hom a) e3

variable {F : Type} [Field F] [NumberField F]

variable {Y : Var F} (M : TrueGeo.Model Y) (B : LB M.X)

theorem le_chart {v : HeightOneSpectrum (𝓞 F)} (e : Ext v) (y : AlgPt Y) (yt : Sp e.O ⟶ M.X)
    (h : spMap e.O.subtype ≫ yt = y.1 ≫ M.j) {i : (B.pull M.j).ι} (hi : ⊤ ≤ yt ⁻¹ᵁ B.U (i PUnit.unit)) :
    ⊤ ≤ y.1 ⁻¹ᵁ (B.pull M.j).U i := fun x _ => Set.mem_iInter.2 fun _ => by
  change (y.1 ≫ M.j) x ∈ B.U (i PUnit.unit)
  rw [← h]
  exact hi (x := spMap e.O.subtype x) trivial

end GlobalTheory.TrueGeo.OfModel
