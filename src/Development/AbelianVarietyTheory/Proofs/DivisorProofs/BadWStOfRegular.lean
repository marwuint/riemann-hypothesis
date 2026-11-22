import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsArchOne
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenRegularCharacters
import Formalism.LocalToGlobal.GlobalTheory.IrreducibleOfCountSizes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullRepTwist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadPartDimLeSumLocalSharesWhittaker
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeightedIdempotentLocalShareBadTuplesLe
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadShareSizeBoundsAlongFamily
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteCuspFormsFiniteRegularRepresentation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelCuspFormsEmbedRegularRepresentationCopie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainEigenspaceShare
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwoLevelFlagDomainCuspFormRanksShiftedWeights
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsWhittakerCharacterPair
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumRangeEqRoots
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinrankIInfKerSemilinearStandardBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EmbedsInRegularRepresentationCopiesComplexEmbedd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeLineMultipleLeFamilyThreshold

open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.BadWOn

open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds

theorem model_bound {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {U C : Type} [Group U] [Finite U]
    [Finite C] [MulAction U C] (M : TwoLevels E r U C) (ka : Wt M.Ψ r) (ρ : Representation ℂ U (M.cusp ka)) (T : ℕ)
    (hρ : IsPullRep M ka ρ)
    (hc : (M.p0 = 0 ∨ M.p0 = r) ∨ (0 < M.p0 ∧ M.p0 < r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧ GlobalTheory.ShareOn.sOf M ≤ T ∧
      LevelHyp (GlobalTheory.ShareOn.sub M ⊥)))
    (H P : Subgroup U) (hH : LevelHyp (GlobalTheory.ShareOn.sub M H)) (hP : LevelHyp (GlobalTheory.ShareOn.sub M P)) (lam : P →* ℂˣ) :
    ∃ n : ℕ, EmbReg ρ H n ∧ (n : ℝ) * Nat.card H ≤ 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by
  rcases hc with hdef | ⟨h0, hr, hA, hs, hbot⟩
  · obtain ⟨-, hrest⟩ := _root_.GlobalTheory.ShareOn.Definite.share_definite E r U C M hdef ka ρ hρ
    obtain ⟨⟨n, hn, hnc⟩, -⟩ := hrest H hH
    have hP2 := (hrest P hP).2 lam
    refine ⟨n, hn, ?_⟩
    have e : (n : ℝ) * Nat.card H = Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast (hnc.trans hP2.symm)
    rw [e]
    have : (0 : ℝ) ≤ Nat.card P * finrank ℂ (eig ρ P lam) := by positivity
    linarith
  · have hR := _root_.GlobalTheory.ShareRanks.ranks E r U C M hbot h0 hr ka T hA hs
    obtain ⟨n, hn, hb⟩ := _root_.GlobalTheory.CuspEmb.cusp_embReg E r U C M ka ρ hρ _ _ hR H hH
    have hS := (_root_.GlobalTheory.ShareEig.share_eig E r U C M ka ρ hρ _ _ hR P hP lam).1
    refine ⟨n, hn, ?_⟩
    have h4 := hR.2.2.2.1
    have hb' : (n : ℝ) * Nat.card H ≤ finrank ℂ (M.cusp (ka + 2 • deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := by
      exact_mod_cast hb
    have hS' : (finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) : ℝ) ≤
        Nat.card P * finrank ℂ (eig ρ P lam) := by exact_mod_cast hS
    calc (n : ℝ) * Nat.card H ≤ _ := hb'
      _ ≤ 2 * finrank ℂ (M.cusp (ka - deMul M.Ψ r M.p0 (GlobalTheory.ShareOn.sOf M))) := h4
      _ ≤ 2 * (Nat.card P * finrank ℂ (eig ρ P lam)) := by linarith
      _ = 2 * Nat.card P * finrank ℂ (eig ρ P lam) := by ring

end GlobalTheory.BadWOn

end
