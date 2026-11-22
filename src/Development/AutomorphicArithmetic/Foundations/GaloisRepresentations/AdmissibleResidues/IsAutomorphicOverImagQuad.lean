import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AdmissibleResidues.SphericalOfHasSat
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Hypotheses2
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.LocIsotypic
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.GalUnitary

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial GlobalTheory.CuspRep UpperTheory.V.Af

namespace UpperTheory.GalN.V

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}

def NoLink (x : GL (Fin n) (Qbar l)) (Q : ℕ) : Prop :=
  ∀ α β : Qbar l, (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot α → (x : Matrix (Fin n) (Fin n) (Qbar l)).charpoly.IsRoot β →
    ∀ k : ℕ, 1 ≤ k → α ^ k ≠ ((Q : Qbar l) * β) ^ k

def UnlinkAt (r : G F Ω →* GL (Fin n) (Qbar l)) (w : HeightOneSpectrum (𝓞 F)) (A : ValuationSubring Ω) : Prop :=
  ∃ (s : G F Ω) (j : ℕ), 1 ≤ j ∧ IsFrob A (normV w ^ j) s ∧ NoLink (r s) (normV w ^ j)

def Unlinked (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ w : HeightOneSpectrum (𝓞 F), ((l : ℕ) : 𝓞 F) ∉ w.asIdeal → ∀ A : ValuationSubring Ω, IsPlaceOver A w →
    (r '' (Ine (F := F) A : Set (G F Ω))).Finite → UnlinkAt r w A

def Wit [IsCMField F] (_ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop := Unlinked r

omit [NumberField F] in

def WitQ (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

def AutCsd0 [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  ∃ π : CuspSub F n, (CG.mk π).IsRegAlg ∧ GlobalTheory.ContraPair.DualIsConj π ∧ AttC ι r π

omit [NumberField F] in

def IsAutomorphicOverImagQuad (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      ∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π

def IsAutCsdN [IsCMField F] (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  AutCsd0 ι r ∧ (Continuous r → Wit ι r)

omit [NumberField F] in

def IsAutQN (ι : Qbar l ≃+* ℂ) (r : G F Ω →* GL (Fin n) (Qbar l)) : Prop :=
  Continuous r → ∀ (K : Type) [Field K] [NumberField K] [IsCMField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω],
    Module.finrank F K = 2 → IsIrr (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) →
      (∃ π : CuspSub K n, (CG.mk π).IsRegAlg ∧ AttC ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω)) π) ∧
        Wit ι (r.comp (AlgEquiv.restrictScalarsHom F : G K Ω →* G F Ω))

section Conv
variable {ι : Qbar l ≃+* ℂ} {r : G F Ω →* GL (Fin n) (Qbar l)}

omit [NumberField F] in
theorem mkQ (h : IsAutomorphicOverImagQuad ι r) (_ : Continuous r → WitQ ι r) : IsAutQ ι r := h
end Conv

end UpperTheory.GalN.V
