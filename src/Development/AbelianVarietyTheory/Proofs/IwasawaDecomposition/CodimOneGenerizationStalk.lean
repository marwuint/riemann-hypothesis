import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StalkGenerizationGermCompat
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLinForms

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef GlobalTheory.Cartier

namespace GlobalTheory.LocalRingGeneralisation

theorem stalk_fromSpecStalk_equiv (X : Scheme.{0}) (x : X) (p : Ideal (X.presheaf.stalk x)) [p.IsPrime] :
    ∃ e : X.presheaf.stalk (X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))) ≃+*
        Localization.AtPrime p,
      ∀ (U : X.Opens) (hq : X.fromSpecStalk x (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x)) ∈ U)
        (hx : x ∈ U) (s : Γ(X, U)),
        e ((X.presheaf.germ U _ hq).hom s) =
          algebraMap (X.presheaf.stalk x) (Localization.AtPrime p) ((X.presheaf.germ U x hx).hom s) := by
  let y : Spec (X.presheaf.stalk x) := (⟨p, inferInstance⟩ : PrimeSpectrum (X.presheaf.stalk x))
  have := isIso_stalkMap_fromSpecStalk X x y
  refine ⟨(asIso ((X.fromSpecStalk x).stalkMap y) ≪≫ Spec.stalkIso _ y).commRingCatIsoToRingEquiv, ?_⟩
  intro U hq hx s
  have h1 := Scheme.Hom.germ_stalkMap_apply (X.fromSpecStalk x) U y hq s
  show (Spec.stalkIso _ y).hom ((X.fromSpecStalk x).stalkMap y ((X.presheaf.germ U _ hq).hom s)) = _
  rw [h1, Scheme.fromSpecStalk_app hx]
  have h2 := congrArg (fun f => f.hom ((Scheme.ΓSpecIso (X.presheaf.stalk x)).inv.hom ((X.presheaf.germ U x hx).hom s)))
    (Spec.germ_stalkMapIso_hom (R := X.presheaf.stalk x) (x := y))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom] at h2
  rw [← CommRingCat.comp_apply (Scheme.ΓSpecIso (X.presheaf.stalk x)).inv (Scheme.ΓSpecIso (X.presheaf.stalk x)).hom,
    Iso.inv_hom_id, CommRingCat.id_apply] at h2
  rw [← h2]
  simp only [← CommRingCat.comp_apply, Category.assoc, TopCat.Presheaf.germ_res]
  erw [TopCat.Presheaf.germ_res]

end GlobalTheory.LocalRingGeneralisation
