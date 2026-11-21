import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionRemovesMaxMultiplicityCells
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MultCellsAmong
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsBaryStageStart
import CompanionTheory.SpectralGeometry.CountingDefinitions.VoronoiMeans.VorFunEvalEqFineMean
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantPolyhedralFan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsStarSubdivision
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsInvariantOrbitCentreMarkingPolyFan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedCentreSet
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.ExistsTwistedSimplicialStarLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsStarSubdivisionInvariantLabelling
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StarSubdivisionNoNewCellOfMaximalMultiplicityFan
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.ConvexCones.StarSubdivisionMultLe

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan GlobalTheory.CompanionTheory.Ar.Fan

namespace GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells

theorem exists_star_drop_multCells : ∀ (O : Type) [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] (bar : O → O) (w0 : O), CMOrd O bar → ∀ (q : ℕ) (φ lab : InvFun O),
    (∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X], Dominates bar X) →
    IsPolyFan bar q φ → IsTwG w0 φ → IsTwG w0 lab → SimpLab bar q φ lab → ∀ M n : ℕ, 2 ≤ M →
    maxMult bar q φ ≤ M → MultCellsAmong bar q φ M (n + 1) →
    ∃ φ' lab' : InvFun O, IsPolyFan bar q φ' ∧ IsTwG w0 φ' ∧ IsTwG w0 lab' ∧ SimpLab bar q φ' lab' ∧
      Subordinate bar q φ' φ ∧ maxMult bar q φ' ≤ M ∧ MultCellsAmong bar q φ' M n := by
  intro O _ _ _ _ bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M n hM hmax hcells
  obtain ⟨R, hR⟩ := hcells
  obtain ⟨w, hwtw, hwc, hcov, hdrop⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedOrbitCentres.centres_exists O bar w0 hb q φ lab hDom hφ hφtw hlabtw hsl M hM hmax (R 0)
  obtain ⟨ψ', hψ', hψ'tw, hsub, hstar⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivision.exists_starSubdivision O bar w0 hb q φ w hDom hφ hφtw hwtw hwc
  obtain ⟨lab', hlab'tw, hsl'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.TwistedStarLabelling.exists_isTwG_simpLab_star O bar w0 hb q φ lab w ψ' hDom hφ hlabtw hsl hwtw hwc hψ' hsub hstar
  obtain ⟨hmax', hc'⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Fan.StarMultiplicity.starMult O bar hb q φ lab w ψ' hDom hφ hsl hwc hdrop hψ' hsub hstar M hmax
  refine ⟨ψ', lab', hψ', hψ'tw, hlab'tw, hsl', hsub, hmax', fun k => R k.succ, ?_⟩
  intro X _ _ _ _ hX m δ hδ
  obtain ⟨hδφ, hnoc⟩ := hc' X hX m δ hδ
  obtain ⟨k, hk⟩ := hR X hX m δ hδφ
  induction k using Fin.cases with
  | zero =>
    obtain ⟨β, hβ, hp, hw1, hin⟩ := hcov X hX m δ hδφ hk
    exact absurd hw1 (hnoc β hβ hp hin)
  | succ k => exact ⟨k, hk⟩

end GlobalTheory.CompanionTheory.Ar.Fan.StarSubdivisionDropsCells
