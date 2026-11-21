import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.ArithmeticCylinders
import Formalism.SharpRestriction.LevelLetterCocycles.ResidualIrreducibleOfTheoremThreePrime
import Formalism.CyclotomicNorms.IrreducibilityOfGoodTuple
import Formalism.PadicSubsetSums.CentralIdempotents.GaloisIrreducibility
import Formalism.GaloisIrreducibility.NoSolvableTransitive
import Formalism.PadicSubsetSums.StableGradedCounts.LocalEstimateIVOfTypeSetWeight
import Formalism.PadicSubsetSums.CentralIdempotents.CentralIdempotentIntegral

noncomputable section

namespace Formalism.MainNotions.N.CuspidalLatticeIdempotents

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain
open scoped ComplexOrder

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial NumberField IsDedekindDomain

theorem algBB_sub (g N : ℕ) (hg : 2 ≤ g) :
    Formalism.CyclotomicNorms.BB N g ⊆ ((Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.BB g N : Finset ℕ) : Set ℕ) := by
  intro l hl
  rw [Finset.mem_coe, Formalism.IrreducibleCountingLemmas.GaloisIrreducibility.mem_BB_iff]
  rcases hl with h | ⟨d, hd1, hdN, hlp, hlt⟩
  · exact Or.inl h
  · refine Or.inr ⟨?_, hlp, d, Finset.mem_Icc.mpr ⟨hd1, hdN⟩, hlt⟩
    have hone : 1 < g ^ d := Nat.one_lt_pow (by omega) (by omega)
    have hv : padicValNat l (g ^ d - 1) ≠ 0 := by
      intro h0
      rw [h0, mul_zero, pow_zero] at hlt
      omega
    have hdvd : l ∣ g ^ d - 1 := by
      by_contra hnd
      exact hv (padicValNat.eq_zero_of_not_dvd hnd)
    have h1 := Nat.le_of_dvd (by omega) hdvd
    have h2 : g ^ d ≤ g ^ N := Nat.pow_le_pow_right (by omega) hdN
    omega

end Formalism.MainNotions.N.CuspidalLatticeIdempotents
