import Mathlib
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LieLatticeData
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeAnnihilatorLatticeHoldsStatement
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeImageLattice
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HodgeDivisorIdealLattice

open GlobalTheory.CompanionTheory.Ar.Num

namespace GlobalTheory.CompanionTheory.Ar.Num

theorem lattice_facts_of_normal : ∀ {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω] {F : Type} [Zero F] [One F] [Fintype F] {n : ℕ} {Sg : Type} {r s : Sg → ℕ} (D : LieLatticeData Ω F n Sg r s) (R : Subalgebra o Ω) (p : ℕ) (w : Ω) (χ : Sg → F → Ω), CharData R p w χ → D.Base R p w → p.Prime → IsNoetherianRing R → IsFractionRing R Ω → IsIntegrallyClosedIn R Ω → ∀ φ : Equiv.Perm Sg, D.TestFacts R p w χ φ → D.Good₁ R p χ → D.Good₂ R p χ → D.Facts R p w χ φ := by
  intro o Ω _ _ _ F _ _ _ n Sg r s D R p w χ hc hb hp hn hf hi φ ht h1 h2
  have hleaf := GlobalTheory.T.hodge_annihilator_lattice_holds D R p w χ hc hb hp hn hf hi φ ht h1
  have hseq := _root_.GlobalTheory.CompanionTheory.Ar.Num.HodgeAnnihilatorSequence.main D R p w χ hc hb hp hn hf hi φ ht h1 h2
  obtain ⟨hdx, honto, hinj⟩ := _root_.GlobalTheory.CompanionTheory.Ar.Num.HaSteps.main D R p w χ hc hb hp hn hf hi φ ht h1 h2
  exact
    { le_af := hleaf
      im := fun τ => (hseq τ).1
      ker := fun τ => (hseq τ).2
      dx := hdx
      onto := honto
      inj := hinj }

end GlobalTheory.CompanionTheory.Ar.Num
