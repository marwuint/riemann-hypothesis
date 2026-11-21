import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedRepConjMaxCompactIntertwines
import Formalism.PeriodIntegrals.DSInfCharCap
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PseudoCoefficientUpqTrivial
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.DiscreteSeriesCharacter
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LanglandsClassification
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Formalism.RealPlaceAnalysis.StatementE
import Formalism.RealPlaceAnalysis.StatementB

open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.derivedRep_conj_maxCompact_intertwines : ∀ (n : ℕ) (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (ρ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Formalism.QuantumDeterminants.IsCRepOn (Formalism.MainNotions.S.UJset ε) ρ → ∀ κ ∈ Formalism.REAL.Kset ε, ∀ X ∈ GlobalTheory.SmoothGlob.lieSet ε, ∀ v : H, Formalism.L2.Theta.SmoothVec (GlobalTheory.SmoothGlob.lieSet ε) ρ v → Formalism.L2.Theta.dRep ρ (κ * X * κ⁻¹) (ρ κ v) = ρ κ (Formalism.L2.Theta.dRep ρ X v) := by
  exact @GlobalTheory.GKLie.dRep_conj_Kset
