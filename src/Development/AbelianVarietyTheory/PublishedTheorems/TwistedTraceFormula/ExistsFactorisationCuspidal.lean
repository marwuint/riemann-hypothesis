import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MemL2OfAutomorphicEmbedding
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompactAdele

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta MeasureTheory IsDedekindDomain NumberField Filter
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace GlobalTheory.AdelicU GlobalTheory.Cusp GlobalTheory.AutMult
open Formalism.MainNotions.KudlaSiegelWeil (Restr)
open Formalism.MainNotions.SchurIrreducible (Pl)
open GlobalTheory.PRep (IsAdmissible fixed)
open scoped InnerProductSpace

namespace GlobalTheory

namespace Flath

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

abbrev finFactor (R : ∀ v, IrrU (GPl σ J v)) (v : HeightOneSpectrum (𝓞 F)) :
    GLoc σ J v →* ((R (.inr v)).H →L[ℂ] (R (.inr v)).H) := (R (.inr v)).π

def IsUnramFactorisation {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] (R : ∀ v, IrrU (GPl σ J v))
    (ξ : ∀ v, (R v).H) (π : GAd σ J →* (H →L[ℂ] H)) (B : (∀ v, (R v).H) → H) : Prop :=
  IsFactorisation σ J (fun v => (R v).π) ξ π B ∧
  (∀ v, (smRep (finFactor R v)).IsIrreducible ∧ IsAdmissible (smRep (finFactor R v))) ∧
  ∀ L : Submodule (𝓞 E) (Fin n → E), Submodule.IsLattice E L →
    ∀ᶠ v in cofinite, fixed (toRep (finFactor R v)) (stabLoc σ J L v) = ℂ ∙ ξ (.inr v)

end Flath

namespace Published

def FlathFactorisation : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J →
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π : GAd σ J →* (H →L[ℂ] H)), IsIrrUnitary π →
        ∃ (R : ∀ v, IrrU (GPl σ J v)) (ξ : ∀ v, (R v).H) (B : (∀ v, (R v).H) → H), Flath.IsUnramFactorisation R ξ π B

namespace FlathFactorisation

end FlathFactorisation

end Published

namespace Flath

end Flath

end GlobalTheory

end
