import Formalism.LocalToGlobal.Columns.Record
import Formalism.LocalToGlobal.Columns.NonDeg
import Formalism.LocalToGlobal.Columns.RecLevelDiv

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Forms

section Triv

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs)

def ChainGlob.triv (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : ChainGlob W σ₀ where
  hσ := hσ
  chr := ⟨fun _ => 1, 1⟩
  chr_unit := ⟨fun _ _ => by simp, fun _ => by simp⟩
  sel := sel
  S := ∅
  ι := Empty
  mu := fun a => a.elim
  L := fun a => a.elim
  twOk := fun a => a.elim

instance (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))
    (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) : IsEmpty (ChainGlob.triv W σ₀ hσ sel).ι :=
  ⟨fun a => Empty.elim a⟩

end Triv

end Formalism.L2.Col
