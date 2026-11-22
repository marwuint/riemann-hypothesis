import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ToRepFam
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorFormallySmoothSquareZeroLiftStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfArtinianSquareZeroLiftingNoetherianBase
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothOfRelativeDimensionOfUniversalFirstOrderTa
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HarrisTaylorObjectPullbackComp
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHarrisTaylorObjectPullback
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniversalTangentHarrisTaylorRepresentingFaStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.UPel.HT

theorem RepFam.smoothOfRelativeDimension : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (R : Type) [CommRing R] [IsNoetherianRing R] (b : Base D R) (N : ℕ), 3 ≤ N → N.Coprime p → ∀ F : RepFam b N, IsQProjOver F.s → SmoothOfRelativeDimension (D.a * (D.n - 1)) F.s := by
  intro p _ D R _ _ b N hN hNp F hq
  have hlft : LocallyOfFiniteType F.s := by
    obtain ⟨M, i, hi, hqc, hi'⟩ := hq
    have := isProper_str R M
    rw [← hi']
    infer_instance
  have hsm : Smooth F.s := by
    refine _root_.GlobalTheory.SmoothCrit.smooth_of_artinian_lift R F.X F.s hlft ?_
    intro C C₀ _ _ _ _ π hπ hker t x₀ hx
    obtain ⟨β, rfl⟩ : ∃ β : R →+* C, t = spMap β :=
      ⟨(Spec.preimage t).hom, by simp [spMap]⟩
    have hcomp : spMap π ≫ spMap β = spMap (π.comp β) := by
      simp [spMap, ← Spec.map_comp]
    have hs₀ : x₀ ≫ F.s = spMap (π.comp β) := by rw [hx, hcomp]
    obtain ⟨o₀, ⟨m₀⟩⟩ := _root_.GlobalTheory.UPel.HT.BaseChange.exists_objMap p D R b N _ _ F.s _ F.univ x₀ hs₀
    obtain ⟨o', ⟨m'⟩⟩ := GlobalTheory.T.harrisTaylor_formally_smooth_squareZero_lift p D R b N hN hNp C C₀ π β hπ (by rw [← hker, pow_two]) o₀
    obtain ⟨x, ⟨hxs, ⟨mx⟩⟩, -⟩ := F.rep (Sp C) (spMap β) o'
    obtain ⟨mc⟩ := _root_.GlobalTheory.UPel.HT.objMap_comp p D R b N _ _ _ _ _ _ o₀ o' F.univ (spMap π) x m' mx
    refine ⟨x, ?_, hxs⟩
    exact (F.rep (Sp C₀) (spMap (π.comp β)) o₀).unique
      ⟨by rw [Category.assoc, hxs, hcomp], ⟨mc⟩⟩ ⟨hs₀, ⟨m₀⟩⟩
  exact _root_.GlobalTheory.SmoothDimTangent.smoothOfRelativeDimension_of_universal_tangent R F.X F.s _ hsm (GlobalTheory.T.exists_universal_tangent_harrisTaylor_representingFamily p D R b N hN hNp F hq hsm)

end GlobalTheory.UPel.HT
