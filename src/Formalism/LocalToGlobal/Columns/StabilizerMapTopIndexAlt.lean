import Formalism.LocalToGlobal.Columns.RecChainYKmap
import Formalism.LocalToGlobal.Columns.StabilizerMapMaximalIndex

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col.Sc.Fr

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker Formalism.L2.Col Formalism.L2.Col.Sc

section Top

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R)
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} (cst : LocCst X (rowSG Pr sel mu)) (L₀ : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (u : Pr.Word) (m2 : ℕ)
  (Λt : ∀ j, LevFam X.E X.K (R.N j) Pr.vGs) (Θt : ∀ j, LevQFam X.E X.K (R.N j) (QE sel (mu : Chr X.F X.E X.K)))
  {SG' : Finset (HeightOneSpectrum (𝓞 X.E))} (hSG : Pr.vGs ⊆ SG') (ΛM : LevFam X.E X.K (R.N R.m - 1) SG')

attribute [local instance] ptYAct

variable (sel mu) in

structure TopFr where
  fr : ∀ (_P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (_d : DecoSet X.E (R.N R.m - 1) ∅ SG'), Sp X.E (R.N R.m) ≃ₗ[X.E] Sp X.E (R.N R.m)
  spec : ∀ P d x, fr P d x ∈ localization₂ P.1.asIdeal (tilR hSG u d).1.N ↔ x ∈ stdAt X.E (R.N R.m) P.1

variable (hm : R.m = m2 + 2) (F : TopFr sel mu u hSG)

def TopLevQ : Prop :=
  ∀ (d : DecoSet X.E (R.N R.m - 1) ∅ SG') (s : (ptGSD W ΛM).G), s • d = d →
    ∀ (P : {P // P ∈ QE sel (mu : Chr X.F X.E X.K)}) (h : (F.fr P d)⁻¹ * (extR R hSG (s.1, s.2.1)).1.1 * F.fr P d ∈ GLint X.E (R.N R.m) P.1),
      (⟨_, h⟩ : ↥(GLint X.E (R.N R.m) P.1)) ∈ (Θt R.m P).H

variable {W cst L₀ u m2 Λt Θt hSG ΛM hm F}

variable (sec : SecY W sel mu cst (L₀.withTop m2 Λt Θt) u m2)

end Top

end Formalism.L2.Col.Sc.Fr
