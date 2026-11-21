import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CharpolyFromTrace.KillTransferAlt
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfTraceMulEqZeroSemisimpleRep
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PolyApproxZeroPadic
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPsCharOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FiniteSemisimple
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.StringRepresentations.WeightsConj
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilRepEquivOfCharpolyEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilDeligneInductionPrinciple

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial
open GlobalTheory.WeilDeligne GlobalTheory.Cong UpperTheory.Gal.NearKilling

private theorem kill_mul (kt : KillTransfer) {I V V' : Type} [Group I] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V'] [FiniteDimensional ℂ V']
    (ρ : Representation ℂ I V) (ρ' : Representation ℂ I V') (hf : (Set.range ρ).Finite)
    (ht : ∀ s, LinearMap.trace ℂ V (ρ s) = LinearMap.trace ℂ V' (ρ' s)) (s γ : I) (a : ℂ) (q : ℂ[X]) :
    ((ρ' s - a • 1) * aeval (ρ' γ) q = 0 → (ρ s - a • 1) * aeval (ρ γ) q = 0) ∧
    (aeval (ρ' γ) q * (ρ' s - a • 1) = 0 → aeval (ρ γ) q * (ρ s - a • 1) = 0) := by
  have key : ∀ {W : Type} [AddCommGroup W] [Module ℂ W] (r : Representation ℂ I W),
      r.asAlgebraHom (MonoidAlgebra.single s 1 - a • 1) = r s - a • 1 ∧
      r.asAlgebraHom (aeval (MonoidAlgebra.single γ (1 : ℂ)) q) = aeval (r γ) q := by
    intro W _ _ r
    refine ⟨?_, ?_⟩
    · rw [map_sub, map_smul, map_one, Representation.asAlgebraHom_single_one]
    · rw [← Polynomial.aeval_algHom_apply, Representation.asAlgebraHom_single_one]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have := kt I V V' ρ ρ' hf ht ((MonoidAlgebra.single s 1 - a • 1) * aeval (MonoidAlgebra.single γ (1 : ℂ)) q)
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this
  · have := kt I V V' ρ ρ' hf ht (aeval (MonoidAlgebra.single γ (1 : ℂ)) q * (MonoidAlgebra.single s 1 - a • 1))
      (by rw [map_mul, (key ρ').1, (key ρ').2]; exact h)
    rwa [map_mul, (key ρ).1, (key ρ).2] at this

