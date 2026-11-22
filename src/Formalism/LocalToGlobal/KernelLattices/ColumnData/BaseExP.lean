import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.IsAdmissibleFlagPairOfUnitriangularLeftAutomorph
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerPerPair
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.OrthogonalDiagonal
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FourSquareQuaternions.QmapInjective
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerSplit
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetOrd
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.KerDetFin
import Formalism.PeriodIntegrals.KerTens
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorSpanning.TensSpans
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.RpOfIsIntegral
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalLatticeIsomorphism.LatticeFromNormOneInduction

noncomputable section
open scoped BigOperators ComplexConjugate Pointwise
open NumberField Formalism.BasicNotions Classical IntermediateField

namespace Formalism.L2.Ker.Cd

open Formalism.MainNotions Formalism.FrobeniusOrbits

section Host

variable {R : Ranks} (H : Host R)

theorem phi_b : H.φ₀ (H.sqd) = Complex.I * (Real.sqrt H.d : ℂ) := H.φ₀_mem

theorem phi_conj (φ : H.E →+* ℂ) (x : H.E) : φ (H.conj x) = conj (φ x) :=
  H.conjE_apply φ x

theorem d_pos : 0 < H.d := H.hyp.2.1.pos

theorem bE_sq : H.sqd ^ 2 = -(H.d : H.E) := H.sqd_sq

theorem b_mem_K : H.sqd ∈ H.K := mem_adjoin_simple_self ℚ _

def bK : H.K := ⟨H.sqd, b_mem_K H⟩

theorem finrank_K : Module.finrank ℚ H.K = 2 := by
  have hint : IsIntegral ℚ H.sqd := .of_finite ℚ _
  have hp : minpoly ℚ H.sqd = Polynomial.X ^ 2 + Polynomial.C (H.d : ℚ) := by
    symm
    apply minpoly.eq_of_irreducible_of_monic
    · apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
      · rw [Polynomial.natDegree_X_pow_add_C]
        simp
      · intro x hx
        simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C] at hx
        have hd : (0 : ℚ) < H.d := by exact_mod_cast d_pos H
        nlinarith [sq_nonneg x]
    · simp [bE_sq H]
    · exact Polynomial.monic_X_pow_add_C _ (by norm_num)
  show Module.finrank ℚ ℚ⟮H.sqd⟯ = 2
  rw [IntermediateField.adjoin.finrank hint, hp, Polynomial.natDegree_X_pow_add_C]

theorem K_induction {p : H.E → Prop} (hb : p (H.sqd)) (hq : ∀ r : ℚ, p (algebraMap ℚ H.E r))
    (hadd : ∀ x y, p x → p y → p (x + y)) (hinv : ∀ x, p x → p x⁻¹) (hmul : ∀ x y, p x → p y → p (x * y))
    (k : H.K) : p (k : H.E) := by
  obtain ⟨k, hk⟩ := k
  show p k
  have hk' : k ∈ IntermediateField.adjoin ℚ {H.sqd} := hk
  clear hk
  induction hk' using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff.mp hx]
    exact hb
  | algebraMap r => exact hq r
  | add x y _ _ hx hy => exact hadd x y hx hy
  | inv x _ hx => exact hinv x hx
  | mul x y _ _ hx hy => exact hmul x y hx hy

theorem conj_conj (x : H.E) : H.conj (H.conj x) = x := by
  apply H.φ₀.injective
  rw [phi_conj, phi_conj, Complex.conj_conj]

theorem emb_on_K (g : R.GG) (hg : g ∈ R.Psi) (k : H.K) : H.emb g (k : H.E) = H.φ₀ (k : H.E) := by
  have hs : (H.sigmaOf g) H.sqd = H.sqd := by
    rw [H.gal_sqd (H.sigmaOf g)]
    have h1 : H.gal (H.sigmaOf g) = g := by
      simp [Formalism.BasicNotions.Host.sigmaOf]
    have h2 : g.1.2 = 1 := hg
    rw [h1, h2]
    simp
  apply K_induction H (p := fun x => H.emb g x = H.φ₀ x)
  · simp [Formalism.BasicNotions.Host.emb, hs]
  · intro r
    simp [Formalism.BasicNotions.Host.emb]
  · intro x y hx hy
    rw [map_add, map_add, hx, hy]
  · intro x hx
    rw [map_inv₀, map_inv₀, hx]
  · intro x y hx hy
    rw [map_mul, map_mul, hx, hy]

theorem phi_nonreal : ∃ k : H.K, (H.φ₀ (k : H.E)).im ≠ 0 := by
  refine ⟨bK H, ?_⟩
  show (H.φ₀ H.sqd).im ≠ 0
  rw [phi_b H]
  have hd : (0 : ℝ) < H.d := by exact_mod_cast d_pos H
  simp [(Real.sqrt_pos.mpr hd).ne']

end Host

section Facts

variable (D : Car)

theorem kQuad : KQuad D := finrank_K D.host
theorem embInj : EmbInj D := fun _ _ h => D.eTau.injective (Subtype.ext ((factEmb D.R D.host).1.1 h))

theorem embOnK : EmbOnK D := fun τ k => emb_on_K D.host _ (D.eTau τ).2 k

theorem phiNonReal : PhiNonReal D := phi_nonreal D.host
end Facts

section Exist

variable {D : Car}

theorem periodExists_of (h2 : KQuad D) (hn : PhiNonReal D) : PeriodExists D :=
  fun cc δ hcc hδ =>
    exists_periodPairOfIdeal D.host.K (D.host.φ₀.comp (algebraMap D.host.K D.host.E)) cc δ h2 hn hcc hδ

end Exist

section Final

variable (D : Car)

theorem periodExists : PeriodExists D := periodExists_of (kQuad D) (phiNonReal D)
end Final

namespace Test

end Test

end Formalism.L2.Ker.Cd
