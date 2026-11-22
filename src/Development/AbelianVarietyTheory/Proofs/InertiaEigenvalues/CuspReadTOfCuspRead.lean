import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CGTrue
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecTExists
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RecTExistsIff
import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.FinIso
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.RecT
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.IsComplementaryProductOfIsCuspidal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StandardCosocleGL
import Formalism.SharpRestriction.LevelLetterCocycles.SphericalInertData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIrreducibleFixed
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsUnitaryOfIsCsd
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CGTrueT

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.HeightCounting

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.RecT

abbrev RecFam : Type 1 :=
  ∀ {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω}
    {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w), IrrGL (w.adicCompletion E) → WD h

set_option synthInstance.maxHeartbeats 400000

variable {R : Ranks} {H : Formalism.BasicNotions.Host R}

def compG {a : ℕ} (π : HostCGu H a) (w : PlE H) : IrrGL (w.adicCompletion H.E) :=
  haveI := host_isCMField H; ⟨a, ParLaws.toCl (π.1.loc w)⟩

def AllGood {a : ℕ} (π : HostCGu H a) : Prop := ∀ w : PlE H, Good (compG π w)

variable {Ω : Type} [Field Ω] [Algebra H.E Ω] [IsAlgClosure H.E Ω]

def locGR (rc : RecFam) (pl : Formalism.GaloisCohomology.Places H.E Ω) {a : ℕ} (π : HostCGu H a) (w : PlE H) : WD (pl.2 w) :=
  rc (pl.2 w) (compG π w)

end GlobalTheory.RecT

namespace GlobalTheory.RecT

open GlobalTheory.RowTie

structure CGTrueT (rc : RecFam) (D : D7) (T : WDTie D.nd D.naut) where
  isRecT : ∀ w, IsRecT (D.nd.plOm.2 w) (rc (D.nd.plOm.2 w))
  e : ∀ a, D.naut.CG a ↪ HostCGu D.host a
  surj : ∀ a, 0 < a → ∀ π : HostCGu D.host a, AllGood π → ∃ σ, e a σ = π
  zero : IsEmpty (D.naut.CG 0)
  loc : ∀ a (π : D.naut.CG a) w, Good (compG (e a π) w) → T.e w (D.naut.locG π w) = locGR rc D.nd.plOm (e a π) w
  tw : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) (χ : D.naut.CG 1), e a (D.naut.tw π χ) = (e a π).tw (e 1 χ)
  inf : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a) τ, D.naut.infG π τ = (e a π).infChar τ
  csd : haveI := host_isCMField D.host; ∀ a (π : D.naut.CG a), D.naut.csd π ↔ (e a π).IsCsd

variable {rc : RecFam} {D : D7} {T : WDTie D.nd D.naut}

def CGTrueT.equivGood (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) :
    {σ : D.naut.CG a // AllGood (C.e a σ)} ≃ {π : HostCGu D.host a // AllGood π} :=
  Equiv.ofBijective (fun σ => ⟨C.e a σ.1, σ.2⟩)
    ⟨fun σ τ hst => Subtype.ext ((C.e a).injective (congrArg Subtype.val hst)),
     fun π => let ⟨σ, hσ⟩ := C.surj a h π.1 π.2; ⟨⟨σ, hσ ▸ π.2⟩, Subtype.ext hσ⟩⟩

@[simp] theorem CGTrueT.equivGood_apply (C : CGTrueT rc D T) (a : ℕ) (h : 0 < a) (σ) :
    (C.equivGood a h σ : HostCGu D.host a) = C.e a σ.1 := rfl

section Read

open Formalism.MainNotions Formalism.MainNotions.N ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 GlobalTheory.UnitaryBC GlobalTheory.FormDict GlobalTheory.DefiniteBC

end Read

end GlobalTheory.RecT

namespace GlobalTheory.RecT

end GlobalTheory.RecT

end
