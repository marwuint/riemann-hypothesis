import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPolynomialInertiaFixedEvalEq
import Development.AbelianVarietyTheory.Definitions.Foundations.HTLawAt
import Development.AbelianVarietyTheory.Statements.CuspidalUnitaryTwists.ZetaUr
import Development.AbelianVarietyTheory.Definitions.Foundations.IsLocallyConstantCycMod
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UnramifiedCocycleKillsRoots
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.EulerSystemTameClassScaleEnlargeCoefficients

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.Col
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_polynomial_eval_eq_of_inertia_fixed : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (A : ValuationSubring Ω) (ζ u : Ω), (∀ s ∈ Ine (F := ℚ) A, s ζ = ζ → s u = u) → ∃ P : Polynomial Ω, (∀ s ∈ Ine (F := ℚ) A, ∀ d, s (P.coeff d) = P.coeff d) ∧ P.eval ζ = u := by
  exact @GlobalTheory.exists_polynomial_inertia_fixed_eval_eq
