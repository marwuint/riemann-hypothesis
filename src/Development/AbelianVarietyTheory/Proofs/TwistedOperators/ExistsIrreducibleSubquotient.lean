import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.MatrixMeasurableSpace
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OpenClosedSequences
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InductionContragredient
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowerEquivUpperSwap
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParIndJacPlacing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CentralExponentBoundOver
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgebraMapIntertwiningMapBijectiveOfIsSmooth

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.BoundaryMaps

section Products

open Matrix

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

theorem piTensor_scalar {α : Type} [Fintype α] {Γ X : α → Type} [∀ a, Group (Γ a)]
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (Γ a) (X a))
    (g : ∀ a, Γ a) (c : α → ℂ) (h : ∀ a x, ρ a (g a) x = c a • x) (y : ⨂[ℂ] a, X a) :
    piTensor ρ g y = (∏ a, c a) • y := by
  induction y using PiTensorProduct.induction_on with
  | add x y hx hy => rw [map_add, hx, hy, smul_add]
  | smul_tprod r x =>
    rw [map_smul, smul_comm, piTensor_tprod, ← MultilinearMap.map_smul_univ]
    simp only [h]

theorem deltaHalf_scalar {α : Type} (m : α → Type) [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] (z : kˣ) :
    deltaHalf k m (fun a => GeneralLinearGroup.scalar (m a) z) = 1 := by
  have h1 : ∀ a, GeneralLinearGroup.det (GeneralLinearGroup.scalar (m a) z) = z ^ Fintype.card (m a) :=
    fun a => by ext; simp [GeneralLinearGroup.scalar]
  have h2 : ∑ a, modExp m a * (Fintype.card (m a) : ℤ) = 0 := by
    simp only [modExp, sub_mul, Finset.sum_sub_distrib, Finset.sum_mul, Finset.sum_filter, ite_mul,
      zero_mul]
    rw [Finset.sum_comm, sub_eq_zero]
    simp only [mul_comm]
  apply Units.ext
  rw [val_deltaHalf, modulus]
  have h3 : ∀ a, nabs k (z ^ Fintype.card (m a)) ^ modExp m a =
      nabs k z ^ (modExp m a * (Fintype.card (m a) : ℤ)) := fun a => by
    rw [mul_comm, _root_.zpow_mul, zpow_natCast]
    simp [nabs]
  simp only [h1, h3, ← Real.rpow_intCast]
  rw [← Real.rpow_sum_of_pos (nabs_pos' k z), ← Int.cast_sum, h2]
  simp

theorem multiProd_scalar {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α] [∀ a, Fintype (m a)]
    [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n] (e : (Σ a, m a) ≃ n) {X : α → Type}
    [∀ a, AddCommGroup (X a)] [∀ a, Module ℂ (X a)] (ρ : ∀ a, Representation ℂ (GL (m a) k) (X a))
    (ω : α → kˣ →* ℂˣ) (h : ∀ a, HasCentralChar (ρ a) (ω a)) (z : kˣ) (f) :
    multiProd e ρ (GeneralLinearGroup.scalar n z) f = (∏ a, (ω a z : ℂ)) • f := by
  have h1 : leviEmb k e (fun a => GeneralLinearGroup.scalar (m a) z) = GeneralLinearGroup.scalar n z := by
    ext i j
    obtain ⟨⟨a, i⟩, rfl⟩ := e.surjective i
    obtain ⟨⟨b, j⟩, rfl⟩ := e.surjective j
    by_cases hab : a = b
    · subst hab
      rw [leviEmb_apply_same]
      simp [GeneralLinearGroup.scalar, diagonal_apply]
    · rw [leviEmb_apply_ne k e _ hab]
      simp [GeneralLinearGroup.scalar, diagonal_apply, hab]
  refine Subtype.ext (Subtype.ext (funext fun x => ?_))
  have h2 := parInd_law e _ f ⟨_, leviEmb_mem_parab k e fun a => GeneralLinearGroup.scalar (m a) z⟩ x
  rw [leviProj_leviEmb, deltaHalf_scalar, piTensor_scalar ρ _ _ fun a => h a z] at h2
  have h3 : x * GeneralLinearGroup.scalar n z = GeneralLinearGroup.scalar n z * x := by
    ext i j
    simp [GeneralLinearGroup.scalar, mul_comm]
  show f.1.1 (x * GeneralLinearGroup.scalar n z) = (_ : ℂ) • f.1.1 x
  rw [h3, ← h1]
  simpa using h2

end Products

end GlobalTheory.BoundaryMaps
