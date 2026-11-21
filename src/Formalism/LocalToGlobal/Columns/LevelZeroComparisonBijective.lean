import Formalism.LocalToGlobal.Columns.DilYStab
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Zero

variable {X : Fields} {Pr : Primes X} {R : Ranks} {W : Wts X Pr.Word R} {Λ : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))} {u : Pr.Word} {m2 : ℕ}

attribute [local instance] ptYAct

theorem frame_move {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {P : HeightOneSpectrum (𝓞 E)} {N N' : Submodule (𝓞 E) (Sp E n)}
    {f f' γ : Sp E n ≃ₗ[E] Sp E n} (hf : ∀ x, f x ∈ localization₂ P.asIdeal N ↔ x ∈ stdAt E n P) (hf' : ∀ x, f' x ∈ localization₂ P.asIdeal N' ↔ x ∈ stdAt E n P)
    (hN : localization₂ P.asIdeal N = localization₂ P.asIdeal (gmap γ N')) : f⁻¹ * γ * f' ∈ GLint E n P := by
  intro x
  show f.symm (γ (f' x)) ∈ stdAt E n P ↔ x ∈ stdAt E n P
  rw [← hf, LinearEquiv.apply_symm_apply, hN, mem_localization_gmap, LinearEquiv.symm_apply_apply, hf']

variable (σ₀ : X.K →+* ℂ) (hσ : ∀ x : X.K, σ₀ (star x) = starRingEnd ℂ (σ₀ x))

end Zero

end Formalism.L2.Col
