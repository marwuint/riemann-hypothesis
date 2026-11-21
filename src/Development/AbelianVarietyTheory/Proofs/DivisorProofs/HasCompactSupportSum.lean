import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExpoConjOfIsCsd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteCompactRep
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemZalgCommuteLieAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteDimensionalSpanCompactOrbitLieDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormDerivativeModerateGrowth
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsCuspidalLieActionOfIsCuspFormStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArchLieDerivativeExists

open NumberField GlobalTheory.CuspRep

noncomputable section

namespace GlobalTheory.CuspStab.LieGrowth

end GlobalTheory.CuspStab.LieGrowth

namespace GlobalTheory.CuspStab

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zfin_of_comm (T : Module.End ℂ (Sm E a)) (hT : ∀ z ∈ Zalg E a, z * T = T * z) {φ : Sm E a}
    (h : FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) '' Zalg E a))) :
    FiniteDimensional ℂ (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z (T φ)) '' Zalg E a)) := by
  refine Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ ((fun z : Module.End ℂ (Sm E a) => z φ) ''
    Zalg E a)).map T) (Submodule.span_le.2 ?_)
  rintro _ ⟨z, hz, rfl⟩
  exact ⟨z φ, Submodule.subset_span ⟨z, hz, rfl⟩, (LinearMap.congr_fun (hT z hz) φ).symm⟩

theorem zalg_comm_fin (k : GL (Fin a) (Af E)) {z : Module.End ℂ (Sm E a)} (hz : z ∈ Zalg E a) :
    z * finRep E a k = finRep E a k * z := by
  let S := Subalgebra.centralizer ℂ ({finRep E a k} : Set (Module.End ℂ (Sm E a)))
  have hL : ∀ X, lie E a X ∈ S := fun X T hT => by
    rw [Set.mem_singleton_iff.1 hT]; exact (lie_rt_fin X k).symm
  have hE : ∀ τ i j, Eop (a := a) τ i j ∈ S := fun τ i j =>
    S.smul_mem (S.sub_mem (hL _) (S.smul_mem (hL _) _)) _
  have hS : Zalg E a ≤ S := by
    refine Algebra.adjoin_le ?_
    rintro _ ⟨τ, u, rfl⟩
    refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.list_prod_mem fun x hx => ?_)
    obtain ⟨m, rfl⟩ := List.mem_ofFn.1 hx
    refine S.add_mem ?_ (hE _ _ _)
    split_ifs
    · exact S.algebraMap_mem _
    · exact S.zero_mem
  exact (hS hz (finRep E a k) rfl).symm

theorem level_of_le {φ ψ : Sm E a} (h : IsOpen {k | finRep E a k φ = φ})
    (hle : ∀ k, finRep E a k φ = φ → finRep E a k ψ = ψ) : IsOpen {k | finRep E a k ψ = ψ} :=
  isOpen_stab_of_mem_nhds _ _ (Filter.mem_of_superset (h.mem_nhds (by simp)) fun k hk => hle k hk)

theorem fin_cpt_comm (k : GL (Fin a) (Af E)) (c : Kinf E a) :
    finRep E a k * cptRep E a c = cptRep E a c * finRep E a k := by
  change rt E a (finGL E a k) * rt E a (infGL E a (Unitary.toUnits c)) =
    rt E a (infGL E a (Unitary.toUnits c)) * rt E a (finGL E a k)
  rw [← map_mul, ← map_mul, infGL_comm]

theorem height_mul_le (c : GL (Fin a) (Cinf E)) : ∃ B : ℝ, 1 ≤ B ∧ ∀ y, height (y * c) ≤ B * height y := by
  refine ⟨1 + ‖rmul (toL c.val)‖ + ‖lmul (toL (c⁻¹).val)‖, by linarith [norm_nonneg (rmul (toL c.val)), norm_nonneg (lmul (toL (c⁻¹).val))], fun y => ?_⟩
  have h1 : toL (y * c).val = rmul (toL c.val) (toL y.val) := rfl
  have h2 : toL ((y * c)⁻¹).val = lmul (toL (c⁻¹).val) (toL (y⁻¹).val) := by
    rw [_root_.mul_inv_rev]; rfl
  have e1 := (rmul (toL c.val)).le_opNorm (toL y.val)
  have e2 := (lmul (toL (c⁻¹).val)).le_opNorm (toL (y⁻¹).val)
  have n1 := norm_nonneg (toL y.val)
  have n2 := norm_nonneg (toL (y⁻¹).val)
  have n3 := norm_nonneg (rmul (toL c.val))
  have n4 := norm_nonneg (lmul (toL (c⁻¹).val))
  unfold height
  rw [h1, h2]
  nlinarith

theorem growth_mul {f : GL (Fin a) (Cinf E) → ℂ} (c : GL (Fin a) (Cinf E))
    (h : ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f y‖ ≤ C * height y ^ N) :
    ∃ (C : ℝ) (N : ℕ), ∀ y, ‖f (y * c)‖ ≤ C * height y ^ N := by
  obtain ⟨C, N, hC⟩ := h
  obtain ⟨B, hB, hB'⟩ := height_mul_le c
  have C0 : 0 ≤ C := by
    have := (norm_nonneg _).trans (hC 1)
    have hp : 0 < height (1 : GL (Fin a) (Cinf E)) ^ N := pow_pos (by linarith [one_le_height (1 : GL (Fin a) (Cinf E))]) N
    exact nonneg_of_mul_nonneg_left this hp
  refine ⟨C * B ^ N, N, fun y => (hC _).trans ?_⟩
  rw [mul_assoc, ← mul_pow]
  exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith [one_le_height (y * c)]) (hB' y) N) C0

end GlobalTheory.CuspStab
