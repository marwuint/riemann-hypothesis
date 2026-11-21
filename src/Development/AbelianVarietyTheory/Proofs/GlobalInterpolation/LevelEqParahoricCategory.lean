import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SandwichNormalForm
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.SourceLatticeInvariance
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.LatticeNormalFormUnipotent
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalFormAtPrime
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UnipotentCharacterArgumentMulStabilizer
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

namespace GlobalTheory.Proof.level_eq_parahoric_category

theorem conj_res {k : Type} [CommRing k] {n c : ℕ} {ρ r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)}
    {γ g : (Fin n → k) ≃ₗ[k] (Fin n → k)} (hγ : ∀ x, ρ (Loc.inX k n c x) = Loc.inX k n c (γ x))
    (hg : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x)) (x : Fin n → k) :
    (ρ⁻¹ * r * ρ) (Loc.inX k n c x) = Loc.inX k n c ((γ⁻¹ * g * γ) x) := by
  show ρ.symm (r (ρ _)) = Loc.inX k n c (γ.symm (g (γ x)))
  rw [hγ, hg, LinearEquiv.symm_apply_eq, hγ, LinearEquiv.apply_symm_apply]

theorem n1Arg_conj_eq {F : Type} [Field F] {n c : ℕ} {ρ r : (Fin (n + c) → F) ≃ₗ[F] (Fin (n + c) → F)}
    (hρ : ρ ∈ Loc.R1 F n c) (hr : r ∈ Loc.R1 F n c) : Loc.n1Arg (ρ⁻¹ * r * ρ) = Loc.n1Arg r := by
  have h1 := unipotentCharacterArgument_mul_stabilizer hρ.1 (mul_mem (mul_mem (inv_mem hρ) hr) hρ).1
  have h2 := unipotentCharacterArgument_mul_stabilizer hr.1 hρ.1
  have e : ρ * (ρ⁻¹ * r * ρ) = r * ρ := by group
  rw [e, h2] at h1
  linear_combination -h1

end GlobalTheory.Proof.level_eq_parahoric_category
