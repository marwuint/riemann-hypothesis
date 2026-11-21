import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfIsOrbFormConst
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPrimitiveBalancedFormPrimitiveAmongIntForms
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PrimitiveIntBilinFormEqOfPositiveRealRay
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMarkedFormPiecesRaysOfSimplicialCells
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsMatchingPiecesOfCell
open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound

theorem orbMark_coord_lt_one : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (φ : InvFun O), IsTwG w0 φ →
  ∀ {X₀ : Type} [AddCommGroup X₀] [Module O X₀] [Module.Finite O X₀] {m₀ : ℕ} (δ₀ : Fin m₀ → LinearMap.BilinForm ℤ X₀) (h₀ : IsCell bar φ δ₀),
  LinearIndependent ℤ δ₀ → (∀ i, IsPrim bar (⟨δ₀ i, h₀.mem i⟩ : balForms bar X₀)) →
  ∀ (v : LinearMap.BilinForm ℤ X₀) (t : Fin m₀ → ℝ), v ≠ 0 → (∀ i, 0 ≤ t i ∧ t i < 1) → toReal v = ∑ i, t i • toReal (δ₀ i) →
  ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m : ℕ) (δ : Fin m → LinearMap.BilinForm ℤ X) (h : IsCell bar φ δ),
    LinearIndependent ℤ δ → (∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) →
    ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → (OrbMark.orbFun O w0 v).evalZ β = 1 →
    ∀ c : Fin m → ℝ, (∀ i, 0 ≤ c i) → toReal β = ∑ i, c i • toReal (δ i) → ∀ i, c i < 1 := by
  intro O _ _ _ _ bar w0 hb φ hφ X₀ _ _ _ m₀ δ₀ h₀ hli₀ hprim₀ v t hv ht hvsum X _ _ _ m δ h hli hprim
    β _ _ hβ1 c hc hβsum j
  obtain ⟨p, -, hpos, hcells⟩ :=
    _root_.GlobalTheory.CompanionTheory.Ar.Fan.MatchingPieces.exists_pieces_match O bar w0 hb φ hφ δ₀ h₀ hli₀ hprim₀ v t hv (fun i => (ht i).1) hvsum β hβ1
  rcases (hc j).lt_or_eq with hcj | hcj
  · obtain ⟨i, hti, d, hd, hpd, hcd⟩ := (hcells m δ h hli c hc hβsum).2 j hcj
    have hpi := (hpos i hti).2.2.1
    have hδj := _root_.GlobalTheory.PolFan.isPrim_eq_one_of_smul_eq bar (δ j) (h.mem j) (hprim j)
    have hd1 := (_root_.GlobalTheory.PrimRay.eq_of_toReal_eq_smul (p i) (δ j) d hd hpi hδj hpd).2
    rw [hcd, hd1, mul_one]
    exact (ht i).2
  · rw [← hcj]; exact zero_lt_one

end GlobalTheory.CompanionTheory.Ar.Fan.OrbitMarkCoordinateBound
