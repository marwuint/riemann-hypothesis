import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarDepthTwistedGalois
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionDepthHostFixingAutInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarDepthToFunNonneg
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionFunctionIntegralStrictlyCon
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StrictStarFunctionBounds
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarFunctionLinearOnCell
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionFunctionLinearOnCells
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.IsStarOfClauses
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionCellMemStarConeOrCentreless
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarIntegralValuesPolyhedral
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolyFanOfStarSubdivisionCells

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.PolCell GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision

theorem isTwG_starFun {O : Type} [CommRing O] [Module.Finite ℤ O] {bar : O → O} {w0 : O} {ψ w : InvFun O}
    (hψ : IsTwG w0 ψ) (hd : IsTwG w0 (starDepth bar ψ w)) (K D : ℕ) :
    IsTwG w0 (starFun bar ψ w K D) := fun σ hσ n B => by
  show _ * (_ * _ + _) = _ * (_ * _ + _)
  rw [hψ σ hσ n B, hd σ hσ n B]

theorem exists_starSubdivision : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (ψ w : InvFun O), (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) → IsPolyFan bar q ψ → IsTwG w0 ψ → IsTwG w0 w → IsCentreSet bar q ψ w → ∃ ψ' : InvFun O, IsPolyFan bar q ψ' ∧ IsTwG w0 ψ' ∧ Subordinate bar q ψ' ψ ∧ IsStarOf bar q ψ w ψ' := by
  intro O _ _ _ _ bar w0 hb q ψ w hDom hψ htψ htw hW
  obtain ⟨K, D, hK, hD, hint, hs1, hs2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StrictStarFunction.exists_starFun_strict O bar hb q ψ w hDom hψ hW
  obtain ⟨hl1, hl2⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarFunctionLinear.starFun_linearOn O bar hb q ψ w K D hW
  have c1 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        (∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → InRCone γ β → w.evalZ β = 0) →
        IsCell bar (starFun bar ψ w K D) γ :=
    fun X _ _ _ _ hX m γ hγ hno => ⟨hγ.mem, hγ.nonneg, hl1 X hX m γ hγ hno, hs1 X hX m γ hγ hno⟩
  have c2 : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X), IsCell bar ψ γ →
        ∀ β₀ ∈ balForms bar X, (∀ y, 0 ≤ β₀ y y) → w.evalZ β₀ = 1 → InRCone γ β₀ →
        ∀ (m' : ℕ) (s : Fin m' ↪ Fin m) (h : LinearMap.BilinForm ℤ X →ₗ[ℤ] ℤ), IsFaceCut γ s h → 0 < h β₀ →
        IsCell bar (starFun bar ψ w K D) (Fin.cons β₀ fun j => γ (s j)) := by
    intro X _ _ _ _ hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos
    refine ⟨fun i => ?_, fun i y => ?_, hl2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos,
      hs2 X hX m γ hγ β₀ hβ₀ hp hw hin m' s h hcut hpos⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hβ₀
      · simpa using hγ.mem (s j)
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hp y
      · simpa using hγ.nonneg (s j) y
  have hstar : IsStarOf bar q ψ w (starFun bar ψ w K D) := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarOfClauses.isStarOf_of_clauses O bar hb q ψ w _ hψ hW c1 c2
  have hpos : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Module.finrank O X ≤ q → ∀ β ∈ balForms bar X, (∀ y, 0 ≤ β y y) → β ≠ 0 →
        0 < (starFun bar ψ w K D).evalZ β := by
    intro X _ _ _ _ hX β hβ hp h0
    rw [starFun_evalZ]
    have h1 := (hψ X hX).pos β hβ hp h0
    have h2 : 0 ≤ (starDepth bar ψ w).evalZ β := starDepth_eval_nonneg _
    have hK' : (0 : ℝ) < K := by exact_mod_cast hK
    have hD' : (0 : ℝ) < D := by exact_mod_cast hD
    positivity
  exact ⟨starFun bar ψ w K D, _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarPolyhedralFan.isPolyFan_star O bar hb q ψ w _ hψ hW hstar hint hpos,
    isTwG_starFun htψ (_root_.GlobalTheory.CompanionTheory.Ar.Fan.StarDepthTwist.isTwG_starDepth O bar w0 hb ψ w htψ htw) K D, _root_.GlobalTheory.PolFan.subordinate_of_isStarOf _ bar q ψ w _ hstar, hstar⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision
