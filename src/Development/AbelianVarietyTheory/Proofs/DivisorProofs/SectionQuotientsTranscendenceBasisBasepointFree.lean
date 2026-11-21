import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsRatioOfWeight
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonvanishingLocusAmpleSectionIsAffineModel
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TranscendenceBasisSectionTupleQuotientsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsIntegralQuotientRingSectionTupleLocus
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProjArithFunctionFieldCharZeroTrdeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularNonvanishingLocusSectionProperties
open CategoryTheory AlgebraicGeometry TopologicalSpace Filter Topology MeasureTheory
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ArInt GlobalTheory.CxPts GlobalTheory.Cartier GlobalTheory.VolBr GlobalTheory.HSAmp

namespace GlobalTheory.HSAmp

theorem gens_quot_trBasis : ∀ (k : Type) [CommRing k] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp k) (D : ℕ), IsArithVar p D → ∀ (P : Pair p), IsAmpleLB P.L.B → ∀ (e : ℕ) (x : Fin (D + 1) → X.functionField), Gens P D e x → (∀ j, x j ≠ 0) ∧ AlgebraicIndependent ℤ (fun j : Fin D => x j.succ / x 0) ∧ FiniteDimensional (ratF x) X.functionField := by
  intro k _ X _ p D hX P hA e x hG
  obtain ⟨l, hl⟩ := hG.cover (genericPoint X)
  have hxl : x l ≠ 0 := ((_root_.GlobalTheory.HSAmp.nv_rules k X p P (e : ℤ) 0 (x l) (hG.mem l)).2.1).1 hl
  obtain ⟨U, hU, hUeq, -, hreg, hft, hfrac, -⟩ :=
    _root_.GlobalTheory.AffModel.main k X p D hX P hA e (x l) hG.pos (hG.mem l) hxl
  obtain ⟨hch, htr⟩ := _root_.GlobalTheory.ArithFnField.charZero_and_trdeg_functionField k X p D hX
  refine GlobalTheory.T.transcendenceBasis_sectionTupleQuotients X.functionField D x l (fnOf U hU).range htr hxl hft ?_ hfrac
  intro w hw
  refine _root_.GlobalTheory.FnInt.main k X p D hX P e x hG l w hxl ?_
  intro z hz
  rw [← hUeq] at hz
  exact (hreg w).2 hw z hz

end GlobalTheory.HSAmp
