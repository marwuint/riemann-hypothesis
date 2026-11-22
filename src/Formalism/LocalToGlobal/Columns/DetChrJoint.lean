import Mathlib
import Formalism.LocalToGlobal.Columns.MuDetOfLoc
import Formalism.LocalToGlobal.Columns.ColumnsProofs.ChainCounts
import Formalism.LocalToGlobal.Columns.HeckeExHost
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.PenultimateKernelDiamondInvariant

open NumberField IsDedekindDomain
open scoped TensorProduct

noncomputable section

namespace Formalism.L2.Col

namespace DetChrL

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.Ker

section Joint

open Classical

variable {X : Fields} {Pr : Primes X}

theorem conjP_vGs (hX : X.Ok) (hPr : Pr.Ok) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∈ Pr.vGs) :
    HeckeExHost.conjPrime₂ P ≠ P ∧ HeckeExHost.conjPrime₂ P ∉ Pr.vGs := by
  have hmem : ∀ j, P ∈ Pr.vG j → X.conjO (Pr.piG j) ∈ P.asIdeal := fun j h => ChainCounts.mem_of_mem_divs h
  have hcomap : ∀ y : 𝓞 X.E, y ∈ (HeckeExHost.conjPrime₂ P).asIdeal ↔ X.conjO y ∈ P.asIdeal := fun y => Iff.rfl
  have hcop : ∀ j, Pr.piG j ∈ P.asIdeal → X.conjO (Pr.piG j) ∈ P.asIdeal → False := by
    intro j h1 h2
    obtain ⟨a, b, hab⟩ := hPr.piG_cop j
    apply P.isPrime.ne_top
    rw [Ideal.eq_top_iff_one, ← hab]
    exact add_mem (Ideal.mul_mem_left _ _ h1) (Ideal.mul_mem_left _ _ h2)
  obtain ⟨i, hi⟩ : ∃ i, P ∈ Pr.vG i := by
    rcases Finset.mem_union.1 hP with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h1 : Pr.piG i ∈ (HeckeExHost.conjPrime₂ P).asIdeal := (hcomap _).2 (hmem i hi)
    rw [h] at h1
    exact hcop i h1 (hmem i hi)
  · obtain ⟨j, hj⟩ : ∃ j, HeckeExHost.conjPrime₂ P ∈ Pr.vG j := by
      rcases Finset.mem_union.1 h with h' | h'
      · exact ⟨0, h'⟩
      · exact ⟨1, h'⟩
    have h1 : Pr.piG j ∈ P.asIdeal := by
      have := (hcomap _).1 (ChainCounts.mem_of_mem_divs hj)
      rwa [HeckeExHost.conjO_conjO'] at this
    by_cases hij : j = i
    · subst hij
      exact hcop j h1 (hmem j hi)
    · have hg1 : ((Pr.g j : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm j]
        exact Ideal.mul_mem_right _ _ h1
      have hg2 : ((Pr.g i : ℕ) : 𝓞 X.E) ∈ P.asIdeal := by
        rw [← hPr.piG_norm i]
        exact Ideal.mul_mem_left _ _ (hmem i hi)
      have hne : Pr.g j ≠ Pr.g i := by
        have key : ∀ a b : Fin 2, a ≠ b → (a = 0 ∧ b = 1) ∨ (a = 1 ∧ b = 0) := by decide
        rcases key j i hij with ⟨h0, h1'⟩ | ⟨h0, h1'⟩
        · rw [h0, h1']; exact hPr.g_ne
        · rw [h0, h1']; exact hPr.g_ne.symm
      have hcopZ : Nat.Coprime (Pr.g j) (Pr.g i) := (Nat.coprime_primes (hPr.g_prime j) (hPr.g_prime i)).2 hne
      obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * (Pr.g j : ℤ) + b * (Pr.g i : ℤ) = 1 := by
        refine ⟨Nat.gcdA (Pr.g j) (Pr.g i), Nat.gcdB (Pr.g j) (Pr.g i), ?_⟩
        have := Nat.gcd_eq_gcd_ab (Pr.g j) (Pr.g i)
        rw [hcopZ] at this
        push_cast at this
        linarith
      apply P.isPrime.ne_top
      rw [Ideal.eq_top_iff_one]
      have e : (1 : 𝓞 X.E) = (a : 𝓞 X.E) * ((Pr.g j : ℕ) : 𝓞 X.E) + (b : 𝓞 X.E) * ((Pr.g i : ℕ) : 𝓞 X.E) := by
        have := congrArg (fun z : ℤ => (z : 𝓞 X.E)) hab
        push_cast at this
        exact this.symm
      rw [e]
      exact add_mem (Ideal.mul_mem_left _ _ hg1) (Ideal.mul_mem_left _ _ hg2)

end Joint

end DetChrL

end Formalism.L2.Col
