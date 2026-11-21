import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsTrans
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsFrameBaseChangeRingHom
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsIsoOfIsProperOfExistsUniqueFieldPointOfIsInteg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNormalisedGraphClosure
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsNatDiagIffIsDiag
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsLiftOfRangeSubset
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartDenseProOpen
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsIsoOfDensePartOfIsIntegral
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsJoinNormalProjectiveModels

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.ModuliIntegralCharts GlobalTheory.ShFam GlobalTheory.LocM

namespace GlobalTheory.LocM.Diag

theorem exists_spMap {A B : Type} [CommRing A] [CommRing B] (x : Sp B ⟶ Sp A) : ∃ g : A →+* B, spMap g = x :=
  ⟨(Spec.preimage x).hom, Spec.map_preimage x⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {Xo : ∀ l : Level H, Moduli Dw l} {p : ℕ} {W : ValuationSubring ℂ} {Y : LocalSystem Xo p W} {i₀ : Idx H p}

theorem frame_at (Z : Mdl Y i₀) {R : Type} [CommRing R] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* R) :
    GlobalTheory.LocM.IsFrame (Y Z.i).t (φ.comp (Z.alg a)) (spMap φ ≫ Z.chart a ≫ Z.π) ((Z.fr a).bc φ) :=
  GlobalTheory.LocM.isFrame_bc E H Dw _ _ _ _ _ _ _ φ _ _ (Z.frame a)

theorem flagAt_chart (Z : Mdl Y i₀) {k : Type} [Field k] (a : Fin Z.m) (φ : Γ(Z.X, (Z.U a).1) →+* k) :
    Z.FlagAt (spMap φ ≫ Z.chart a) ((Z.fr a).bc φ) :=
  ⟨a, φ, rfl, by rw [Category.assoc]; exact frame_at Z a φ,
    SameFlag.refl fun τ i => by rw [Category.assoc]; exact ((frame_at Z a φ).1 τ i).1⟩

variable {Z₁ Z₂ : Mdl Y i₀} {τ : (Y Z₁.i).X ⟶ (Y Z₂.i).X} (mu : SABMap (Y Z₁.i).t (Y Z₂.i).t τ)

variable (hc : GlobalTheory.LocM.Corr Z₁ Z₂) {b : Z₂.i.c.V W →+* Z₁.i.c.V W} (hb : IsIncl b)
  (hτ : τ ≫ (Y Z₂.i).s = (Y Z₁.i).s ≫ spMap b)

variable {r : (Xo Z₁.i.l).XF Z₁.i.c ⟶ (Xo Z₂.i.l).XF Z₂.i.c} (hr : (Y Z₁.i).j ≫ τ = r ≫ (Y Z₂.i).j)

end GlobalTheory.LocM.Diag
