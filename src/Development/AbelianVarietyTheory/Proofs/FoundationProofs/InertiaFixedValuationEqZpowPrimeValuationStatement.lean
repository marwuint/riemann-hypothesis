import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InertiaFixedValuationEqZpowPrimeValuation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ PowerSeries
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.inertia_fixed_valuation_eq_zpow_prime_valuation : ∀ (l : ℕ) [Fact l.Prime] (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω), OverL l A → ∀ x : Ω, x ≠ 0 → (∀ s ∈ Ine (F := ℚ) A, s x = x) → ∃ k : ℤ, A.valuation x = A.valuation (l : Ω) ^ k := by
  exact @GlobalTheory.InertiaFieldUnram.valuation_eq_zpow
