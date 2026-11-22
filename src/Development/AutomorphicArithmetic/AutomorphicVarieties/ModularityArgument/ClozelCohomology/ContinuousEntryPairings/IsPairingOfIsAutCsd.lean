import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClozelCohomology.ContinuousEntryPairings.LocFixed
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.BcPolar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SatakeParametersComplexConjugate
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeDualRep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ConjOpInvolutive

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep GlobalTheory.HeckeGal
open GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Bc UpperTheory.V.Af.Gu UpperTheory.V.Published GlobalTheory.MonoConj
open scoped Matrix

private theorem ss_comp {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (f : Γ →* Γ)
    (hf : Function.Surjective f) (h : IsSSRep r) : IsSSRep (r.comp f) := by
  intro W hW
  obtain ⟨W', hW', hc⟩ := h W fun g v hv => by
    obtain ⟨g, rfl⟩ := hf g
    exact hW g v hv
  exact ⟨W', fun g v hv => hW' (f g) v hv, hc⟩

