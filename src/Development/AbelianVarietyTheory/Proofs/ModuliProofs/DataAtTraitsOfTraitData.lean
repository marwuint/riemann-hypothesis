import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.LocalFramePowerSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ValuationExtension
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TraitDataIntrinsic

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D : Datum H} {l : Level H} {Xo : Moduli D l}
  {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F} (Y : Model Xo c β)

theorem j_s : Y.j ≫ Y.s = pullback.snd _ _ ≫ spMap β := by
  rw [Model.j, Category.assoc, pullback.condition, ← Category.assoc, Y.jQ_over]

theorem exists_generic {S T : Scheme.{0}} {i : T ⟶ S} {χ : S ⟶ Y.X} {t : SAB H S} (m : SABMap t Y.t χ) {v : T ⟶ Xo.XF c}
    (hv : v ≫ Y.j = i ≫ χ) : ∃ (t' : SAB H T) (m₁ : SABMap t' t i) (n : SABMap t' Y.oF.t v)
      (m₂ : SABMap t' Xo.univ.t (v ≫ pullback.fst _ _)), m₁.φ ≫ m.φ = n.φ ≫ Y.m.φ ∧ m₂.φ = n.φ ≫ Y.m0.toSABMap.φ := by
  obtain ⟨t', ⟨p⟩⟩ := (GlobalTheory.ModelPoints.model_points_charts E H D l Xo c O β Y).2.1 _ (i ≫ χ)
  obtain ⟨m₁, h₁⟩ := GlobalTheory.ObjMaps.exists_sab_cancel m p
  have key : ∀ u : T ⟶ Y.X, v ≫ Y.j = u → ∀ p : SABMap t' Y.t u, ∃ n : SABMap t' Y.oF.t v, p.φ = n.φ ≫ Y.m.φ := by
    rintro _ rfl p
    exact GlobalTheory.ObjMaps.exists_sab_cancel Y.m p
  obtain ⟨n, hn⟩ := key _ hv p
  obtain ⟨m₂, h₂⟩ := GlobalTheory.ObjMaps.exists_sab_comp Y.m0.toSABMap n
  exact ⟨t', m₁, n, m₂, h₁.symm.trans hn, h₂⟩

end GlobalTheory.TraitDataIntrinsic
