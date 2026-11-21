import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.SiegelToroidalIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.InterNumDetNonposSplitTorus
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.IntegralBound
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsCoordAtPoints
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormalizedPointHeightLatticeSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KerConstantCoeffEqSpan
import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
import Development.AbelianVarietyTheory.Definitions.Divisors.IsHomWeightHomWeight
import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
import Development.AbelianVarietyTheory.Definitions.Divisors.QuoIff
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostBoundHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUniformHeightConstant
import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
import Formalism.LocalRingCardinality.DataParamsT
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeLevelCharacterBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SizeBoundsForFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevPhInjectiveOfLevDetNonZeroDivisor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspPhMemChiLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SumSqNormWCuspPhLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CardMulRkKChiLatLeRankW

open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
open ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions.TH

namespace GlobalTheory.CovTop.DescentMaps

theorem mapsCore {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H} {l : Level H}
    {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {D : D7} {x : ℝ}
    {V : (c.F →+* ℂ) → HSp D} {dict : ∀ σ, GA D (V σ) → Σ k, Frame ((U σ).X k).Ψ r}
    (S : Subgroup (LevelAut Dw l)) (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M) (Gm W G : WTZ E) (hGW : Gm + W = G)
    (hGm : Even Gm.2) (hW : Even W.2) (hKG : KeepsCusp U G) (hKW : KeepsCusp U W)
    (hLG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U G → g ∈ latW U G)
    (hLW : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U W), (g : Rul Xo c) = pull Xo c γ f → f ∈ latW U W → g ∈ latW U W)
    (hNG : ∀ (γ : LevelAut Dw l) (f g : cuspW Xo c U G), (g : Rul Xo c) = pull Xo c γ f →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict G σ g = GlobalTheory.AllWt.normW U x V dict G σ f)
    (hGood : GoodW U x V dict G) (hGoodP : GoodW U x V dict (G + W))
    (χ : S →* (c.F)ˣ) (u : cuspW Xo c U W) (hu : u ∈ latW U W)
    (hdet : ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (γ : LevelAut Dw l) (f : cuspW Xo c U Gm) (g : cuspW Xo c U (Gm + W)), (g : Rul Xo c) = f * pull Xo c γ u →
      ∀ σ, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ g ≤ B * GlobalTheory.AllWt.normW U x V dict Gm σ f)
    (b : ℝ) (hb : (Fintype.card S : ℝ) ^ 3 * B ^ 2 ≤ Real.exp (2 * b))
    (Lt : Submodule (𝓞 c.F) (cuspW Xo c U G)) (hLt : Lt = GlobalTheory.LevDesc.chiLat S U G χ) (Gp : WTZ E) (hGp : G + W = Gp) :
    ∃ (n : ℕ) (φ : Fin n → cuspW Xo c U Gm →ₗ[c.F] cuspW Xo c U G),
      (∀ h, ∀ f ∈ latW U Gm, φ h f ∈ Lt) ∧ (∀ f, (∀ h, φ h f = 0) → f = 0) ∧
      (∀ σ f, ∑ h, GlobalTheory.AllWt.normW U x V dict G σ (φ h f) ^ 2 ≤
        Real.exp (2 * b) * GlobalTheory.AllWt.normW U x V dict Gm σ f ^ 2) ∧
      n * Formalism.HN.rkK Lt ≤ rankW U Gp := by
  subst hGW hLt hGp
  have hm : ∀ f ∈ cuspW Xo c U Gm, ∀ h : S, GlobalTheory.LevDesc.levPh Xo c S χ (u : Rul Xo c) f h ∈ cuspW Xo c U (Gm + W) :=
    fun f hf h => GlobalTheory.SlopeRec.levPh_mem_cuspW hGm hW hKG hKW χ u.2 hf h
  let e : Fin (Fintype.card S) ≃ S := (Fintype.equivFin S).symm
  refine ⟨Fintype.card S, fun k => LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm, ?_, ?_, ?_, ?_⟩
  · intro k f hf
    exact GlobalTheory.LevDesc.cuspPh_mem_chiLat Xo c U S hpq hA Gm W hGm hW hKG hKW hLG hLW χ u hu f hf (e k)
  · intro f hf0
    have hsec : (f : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ f.2)
    have husec : (u : Rul Xo c) ∈ secRing Xo c :=
      GlobalTheory.LevDesc.mem_secRing (GlobalTheory.AllWt.cuspW_le_secZ _ u.2)
    apply Subtype.ext
    refine GlobalTheory.levPh_injective_of_levDet_nonZeroDivisor Xo c S hpq hA χ u husec hdet _ hsec fun h => ?_
    have h1 := hf0 (e.symm h)
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_proj, Function.eval, Equiv.apply_symm_apply] at h1
    rw [← GlobalTheory.LevDesc.coe_cuspPh S χ _ hm f h, h1]
    rfl
  · intro σ f
    have h1 : ∑ k, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ ((LinearMap.proj (e k) ∘ₗ GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm) f) ^ 2 =
        ∑ h : S, GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2 :=
      e.sum_comp (fun h : S => GlobalTheory.AllWt.normW U x V dict (Gm + W) σ (GlobalTheory.LevDesc.cuspPh S χ (u : Rul Xo c) hm f h) ^ 2)
    rw [h1]
    refine (GlobalTheory.sum_sq_normW_cuspPh_le Xo c U x V dict S hpq hA Gm W hGm hW hKG hKW χ u B hB0 hGood.1 hNG hB f σ).trans ?_
    exact mul_le_mul_of_nonneg_right hb (sq_nonneg _)
  · exact GlobalTheory.CovolRank.card_mul_rkK_chiLat_le_rankW Xo c U x V dict S hpq hA (Gm + W) W (hGm.add hW) hW hKG hKW hGood hGoodP χ u hdet

end GlobalTheory.CovTop.DescentMaps

namespace GlobalTheory.CovTop.DescentMaps

end GlobalTheory.CovTop.DescentMaps
