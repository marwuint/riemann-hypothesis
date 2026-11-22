import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsOfIsDSPar
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CasimirEqGelfandValueOfInfinitesimalCharacter
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SecondGelfandInvariantValueEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.HighestWeightLineOfKTypeMultiplicityOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.InConeOfKTypesAbove

open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible Formalism.L2.Theta Matrix GlobalTheory.RealPar GlobalTheory.CoverDS
open GlobalTheory.IndefiniteRowSideFullHecke.IsotypicSignedParameters (SignedPar IsDSPar)
open Formalism.MainNotions.S (IsURepOn IsIrredOn IsKFin IsKStableOn IsWtOn IsKTypeOf IsDS IsSqIntOn UJset)

namespace GlobalTheory.CoverDS

theorem hasTypes_of_factors : GlobalTheory.Dec.LowKMultOne → GlobalTheory.Dec.KTypesAbove → GlobalTheory.Dec.DSInfChar →
    ∀ (p q n : ℕ) (e : Ix p q ≃ Fin n) (P : SignedPar n) (T : GrpData p q) (R : DSRep T)
      (σ : Matrix (Fin n) (Fin n) ℂ → (R.U.H →L[ℂ] R.U.H)),
      BlockOrd e P.sgn → Factors R.U e σ → IsDSPar P σ → HasTypes R (blockPar P e) := by
  intro h1 h2 h3 p q n e P T R σ hb hf hd
  have hc : ∀ a, ((blockPar P e a : ℚ) : ℝ) = P.lam (e a) := fun a => ratEntry_cast P (e a)
  have hlow : (fun i => ((blattner (blockPar P e) (e.symm i) : ℚ) : ℝ)) = Formalism.QuantumDeterminants.lowK P.sgn P.lam := by
    funext i
    rw [blattner_eq P hb hc, e.apply_symm_apply]
    rfl
  have hn : p + q = n := by simpa using Fintype.card_congr e
  refine ⟨?_, fun v => ?_, GlobalTheory.CoverCone.inCone_of_kTypesAbove h2 p q n e P T R σ hb hf hd⟩
  · refine _root_.GlobalTheory.RealPar.HwLine.finrank_hwSub_eq_one p q n e P.sgn T R σ hb hf _ ?_ ?_
    · rw [hlow]
      exact hd.2.2.2.2.2.1
    · rw [hlow]
      exact h1 n P.sgn P.lam _ σ P.hc hd
  · rw [_root_.GlobalTheory.CoverDS.casimir_eq_gelfVal_of_hasInfChar p q n e P.sgn T R σ hb hf _ (h3 n P.sgn P.lam _ σ P.hc hd) v, _root_.GlobalTheory.GelfandTwo.gelfVal_two, hn]
    congr 1
    have hc' : ∀ a, ((blockPar P e a : ℚ) : ℂ) = ((P.lam (e a) : ℝ) : ℂ) := fun a => by
      rw [← hc a]; simp
    rw [normSq]
    push_cast
    simp only [hc']
    rw [Equiv.sum_comp e (fun a => ((P.lam a : ℝ) : ℂ) ^ 2)]

end GlobalTheory.CoverDS
