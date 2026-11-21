import Formalism.LocalToGlobal.Columns.RecChainUnfOne

open NumberField IsDedekindDomain Module
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Loc

variable {X : Fields} {Pr : Primes X} {R : Ranks}

structure DetChr.Loc (Dc : DetChr X R.m) (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
    (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (σ : X.E →ₐ[X.F] X.E) : Prop where
  trivF : ∀ i, i < R.m → (Formalism.L2.DIV.h90 σ).ker ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  unr : ∀ i, i < R.m → ∀ y ∈ intU X.F X.E,
    (∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal → Units.map (Formalism.UG.prV (E := X.E) v).toMonoidHom y = 1) →
    (Dc.muAt i * (mu : Chr X.F X.E X.K)) y = 1
  unif : ∀ i, i < R.m → ∀ P : HeightOneSpectrum (𝓞 X.E),
    (¬ ∃ P' ∈ rowSG Pr sel mu, P'.asIdeal.under (𝓞 X.F) = P.asIdeal.under (𝓞 X.F)) →
    IsUnifVal (Dc.muAt i * (mu : Chr X.F X.E X.K)) P (mUof Ch mu i P)⁻¹
  tame : ∀ i, i < R.m → ∀ P ∈ rowSG Pr sel mu, ∀ v : HeightOneSpectrum (𝓞 X.F), P.asIdeal.under (𝓞 X.F) = v.asIdeal →
    wildAt X.E v ≤ (Dc.muAt i * (mu : Chr X.F X.E X.K)).ker
  res : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu,
    IsResChar (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1
      (open Classical in if P.1 ∈ Pr.vGs then (chiP Ch P.1 i)⁻¹ else resChar (mu : Chr X.F X.E X.K) P.1)
  atq : ∀ i, i < R.m → ∀ (P : rowSG Pr sel mu) (k : X.Kˣ), IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k →
    cst.muq (i + 1) P = ((k⁻¹ : X.Kˣ) : X.K)
  atq_ex : ∀ i, i < R.m → ∀ P : rowSG Pr sel mu, ∃ k : X.Kˣ, IsQValC (Dc.muAt i * (mu : Chr X.F X.E X.K)) P.1 k
  trivChi : (Formalism.L2.DIV.h90 σ).ker ≤ Dc.chi.ker
  unrChi : ∀ y ∈ intU X.F X.E, Dc.chi y = 1

end Loc

end Formalism.L2.Col
