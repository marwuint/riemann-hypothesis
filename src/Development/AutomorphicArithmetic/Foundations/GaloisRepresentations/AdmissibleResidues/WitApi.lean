import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.AdmissibleRankThreeStrengthen
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.LocDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyConjGlAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.IsRootCharpolySmul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.CharpolyRootPow
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.CharpolyConjugation.Wdown
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.IsAutomorphicOverImagQuad
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.JacquetShalikaBound
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SatakeParametersOfTwist
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.FixedDvd
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LevelIso
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SatakeMatchBaseChange
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.IsAlgChar
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible

noncomputable section

open NumberField IsDedekindDomain Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory GlobalTheory.WeilDeligne GlobalTheory.CuspRep GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private isIrr_iso from Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.SymmetricCubeIrreducible

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {ι : Qbar l ≃+* ℂ} {r r' : G F Ω →* GL (Fin n) (Qbar l)}

def IsRegAlgAutomorphicAttached [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ AttC ι r π

theorem AutCsd0.c0 [IsCMField F] (h : AutCsd0 ι r) : IsRegAlgAutomorphicAttached ι r := h.imp fun _ k => ⟨k.1, k.2.2⟩
variable [IsAlgClosure F Ω]

theorem Wit.iso [IsCMField F] (e : RepIso r r') (h : Wit ι r) : Wit ι r' := L.wiso F Ω l n r r' e h

theorem Wit.tw [IsCMField F] (_P : Hypotheses₂) {μ : G F Ω →* (Qbar l)ˣ} (_hμ : IsAlgChar ι μ) (hc : Continuous μ) (_ha : IsRegAlgAutomorphicAttached ι r)
    (h : Wit ι r) : Wit ι (Af.tw r μ) := L.wtw F Ω l n r μ hc h

section
variable (K : Type) [Field K] [NumberField K] [IsCMField F] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω]

theorem Wit.down (_P : Hypotheses₂) [IsGalois F K] (_hs : Group.IsSolvable (K ≃ₐ[F] K)) (_hc : Continuous r) (_ha : IsRegAlgAutomorphicAttached ι r)
    (_hb : IsRegAlgAutomorphicAttached ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)))
    (h : Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))) : Wit ι r := L.wdown F Ω l n r K h
end

end UpperTheory.GalN.V
