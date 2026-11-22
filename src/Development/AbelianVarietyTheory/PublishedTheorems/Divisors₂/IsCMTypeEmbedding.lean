import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HeckeFunctionalEquationAbs
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetCharEqOneOfHasWt

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.CMVal GlobalTheory.IndefiniteRowSideFullHecke.CompletedLStripBounds

namespace GlobalTheory.Published.HeckeFEModel

section
variable {E : Type} [Field E] [NumberField E]

theorem exists_exponents (χ : HChar E) : ∃ a : HeightOneSpectrum (𝓞 E) →₀ ℕ, ∀ v, ExpAt χ v (a v) := by
  classical
  obtain ⟨h1, h2⟩ := GlobalTheory.Mem.UnrAe.unr_ae_and_level E χ
  have hE : ∀ v, ExpAt χ v (Nat.find (h2 v)) := fun v m => by
    refine ⟨fun h => Nat.find_min' _ h, fun h x hx hx' => Nat.find_spec (h2 v) x hx (hx'.trans ?_)⟩
    rw [WithZero.exp_le_exp]
    omega
  refine ⟨Finsupp.ofSupportFinite (fun v => Nat.find (h2 v)) (h1.subset fun v hv hu => hv ?_), fun v => hE v⟩
  exact (hE v).unique ((expAt_zero_iff χ v).2 hu)

theorem hasInf_inv {I : Type} [Fintype I] {φ : I → E →+* ℂ} {χ : HChar E} {n : I → ℤ}
    (h : Formalism.L2.Host.HChar.HasInf χ φ n) : Formalism.L2.Host.HChar.HasInf χ⁻¹ φ (fun i => -n i) := fun k => by
  rw [Formalism.L2.Host.HChar.inf_inv, Units.val_inv_eq_inv_val, h k, ← Finset.prod_inv_distrib]
  simp only [zpow_neg]

theorem isUnitary_inv {χ : HChar E} (h : IsUnitary χ) : IsUnitary χ⁻¹ := fun x => by
  show ‖(((χ.1 x)⁻¹ : ℂˣ) : ℂ)‖ = 1
  rw [Units.val_inv_eq_inv_val, norm_inv, h x, inv_one]

theorem zero_iff (h : HeckeFunctionalEquationAbs) [IsTotallyComplex E] {I : Type} [Fintype I] {φ : I → E →+* ℂ}
    (hφ : IsCMType φ) {χ : HChar E} {n : I → ℤ} {Λ Λ' : ℂ → ℂ} (hu : IsUnitary χ)
    (hi : Formalism.L2.Host.HChar.HasInf χ φ n) (hn : ∃ i, n i ≠ 0) (h1 : IsCompletedL χ n Λ)
    (h2 : IsCompletedL χ⁻¹ (fun i => -n i) Λ') (s : ℂ) : Λ s = 0 ↔ Λ' (1 - s) = 0 := by
  obtain ⟨a, ha⟩ := exists_exponents χ
  obtain ⟨ε, hε, hs⟩ := h E I φ hφ χ n a Λ Λ' hu hi hn ha h1 h2
  have h0 : ε ≠ 0 := by rintro rfl; simp at hε
  have hA : ((((discr E).natAbs * a.prod fun v k => Ideal.absNorm v.asIdeal ^ k : ℕ) : ℂ)) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    refine mul_ne_zero (Int.natAbs_ne_zero.2 (discr_ne_zero E)) ?_
    exact Finset.prod_ne_zero_iff.2 fun v _ => pow_ne_zero _ (by rw [Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
  rw [hs s, mul_eq_zero, mul_eq_zero, Complex.cpow_eq_zero_iff]
  tauto

end

end GlobalTheory.Published.HeckeFEModel

end
