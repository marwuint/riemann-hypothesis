import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealizationEmbeddingCompatible
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.BigOn.Exp
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open Formalism.IndefR.FWT GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.IndefiniteRowSideFullHecke.ToricLatticeDenominators (FmExt eExt incl)
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.BigOn.Exp

section ScalarGeneric

variable {O : Type} [CommRing O] [IsDomain O] {M : Type} [AddCommGroup M] [Module (FractionRing O) M] [Module O M]
  [IsScalarTower O (FractionRing O) M] [FiniteDimensional (FractionRing O) M]
  {L : Type} [Field L] [Algebra O L] {eK : FractionRing O →+* ℂ} {G : Type}

theorem exists_smul_eq_sum_tmul_finBasis (x : L ⊗[O] M) : ∃ d : O, d ≠ 0 ∧
    ∃ c : _ → L, d • x = ∑ a, c a ⊗ₜ Module.finBasis (FractionRing O) M a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨1, one_ne_zero, 0, by simp⟩
  | add x y hx hy =>
    obtain ⟨d, hd, c, e⟩ := hx
    obtain ⟨d', hd', c', e'⟩ := hy
    refine ⟨d * d', mul_ne_zero hd hd', d' • c + d • c', ?_⟩
    rw [smul_add, mul_smul d d' y, mul_comm, mul_smul, e, e']
    simp [Finset.smul_sum, TensorProduct.add_tmul, Finset.sum_add_distrib, TensorProduct.smul_tmul']
  | tmul a f =>
    obtain ⟨d, hd⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors O)
      fun c => (Module.finBasis (FractionRing O) M).repr f c
    choose y hy using hd
    refine ⟨d, nonZeroDivisors.coe_ne_zero d, fun c => y c • a, ?_⟩
    rw [← TensorProduct.tmul_smul]
    conv_lhs => rw [← (Module.finBasis (FractionRing O) M).sum_repr f]
    rw [Finset.smul_sum, TensorProduct.tmul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [TensorProduct.smul_tmul, ← algebraMap_smul (FractionRing O) (y c), hy, smul_assoc]

variable (rd : M →ₛₗ[eK] (G → ℂ)) (eL : L →+* ℂ)
  (hL : ∀ c : O, eL (algebraMap O L c) = eK (algebraMap O (FractionRing O) c))

theorem readExt_scalar_mem_range
    (hF : ∀ (n : ℕ) (v : Fin n → M), LinearIndependent (FractionRing O) v → LinearIndependent ℂ fun c => rd (v c))
    (x₁ x₂ : L ⊗[O] M) (κ : ℂ) (h : readExt rd eL hL x₁ = κ • readExt rd eL hL x₂) (h₂ : readExt rd eL hL x₂ ≠ 0) :
    ∃ b : L, eL b = κ := by
  set v := Module.finBasis (FractionRing O) M
  have hδ : ∀ d : O, d ≠ 0 → eL (algebraMap O L d) ≠ 0 := fun d hd => by
    rw [hL]
    exact (map_ne_zero eK).2 ((map_ne_zero_iff _ (IsFractionRing.injective O (FractionRing O))).2 hd)
  have hsum : ∀ x : L ⊗[O] M, ∀ (d : O) (c : _ → L), d • x = ∑ a, c a ⊗ₜ v a →
      ∑ a, eL (c a) • rd (v a) = eL (algebraMap O L d) • readExt rd eL hL x := fun x d c e => by
    have := congrArg (readExt rd eL hL) e
    rw [← algebraMap_smul L d x, readExt_smul, map_sum] at this
    rw [this]
    rfl
  obtain ⟨d₁, hd₁, c₁, e₁⟩ := exists_smul_eq_sum_tmul_finBasis x₁
  obtain ⟨d₂, hd₂, c₂, e₂⟩ := exists_smul_eq_sum_tmul_finBasis x₂
  have r₁ := hsum _ _ _ e₁
  have r₂ := hsum _ _ _ e₂
  set δ₁ := eL (algebraMap O L d₁)
  set δ₂ := eL (algebraMap O L d₂)
  have h0 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) = 0 := by
    have e3 : ∑ a, (eL (c₁ a) - δ₁ * κ * δ₂⁻¹ * eL (c₂ a)) • rd (v a) =
        ∑ a, eL (c₁ a) • rd (v a) - (δ₁ * κ * δ₂⁻¹) • ∑ a, eL (c₂ a) • rd (v a) := by
      simp only [sub_smul, Finset.sum_sub_distrib, Finset.smul_sum, mul_smul]
    rw [e3, r₁, r₂, h, smul_smul, smul_smul, inv_mul_cancel_right₀ (hδ _ hd₂), sub_self]
  have hc := Fintype.linearIndependent_iff.1 (hF _ v v.linearIndependent) _ h0
  obtain ⟨a, ha⟩ : ∃ a, c₂ a ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply h₂
    have : δ₂ • readExt rd eL hL x₂ = 0 := by rw [← r₂]; simp [hne]
    exact (smul_eq_zero.1 this).resolve_left (hδ _ hd₂)
  have hca : eL (c₂ a) ≠ 0 := (map_ne_zero eL).2 ha
  refine ⟨c₁ a * algebraMap O L d₂ / (algebraMap O L d₁ * c₂ a), ?_⟩
  have e := sub_eq_zero.1 (hc a)
  rw [map_div₀, map_mul, map_mul, e]
  have h1 : δ₁ ≠ 0 := hδ _ hd₁
  have h2 : δ₂ ≠ 0 := hδ _ hd₂
  change δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ / (δ₁ * eL (c₂ a)) = κ
  rw [div_eq_iff (mul_ne_zero h1 hca)]
  calc δ₁ * κ * δ₂⁻¹ * eL (c₂ a) * δ₂ = δ₁ * κ * eL (c₂ a) * (δ₂⁻¹ * δ₂) := by ring
    _ = κ * (δ₁ * eL (c₂ a)) := by rw [inv_mul_cancel₀ h2]; ring

end ScalarGeneric

theorem exists_algebraMap_eq_of_isIntegral {R : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
    (e : FractionRing R →+* ℂ) (b₀ : FractionRing R) (N : ℕ) (hN : IsUnit (N : R)) (m : ℕ)
    (h : IsIntegral ℤ ((N : ℂ) ^ m * e b₀)) : ∃ b : R, algebraMap R (FractionRing R) b = b₀ := by
  let f : FractionRing R →ₐ[ℤ] ℂ := { e with commutes' := fun r => by simp }
  have e1 : (N : ℂ) ^ m * e b₀ = f ((N : FractionRing R) ^ m * b₀) := by
    simp [f, map_mul, map_pow, map_natCast]
  rw [e1] at h
  have h' : IsIntegral ℤ ((N : FractionRing R) ^ m * b₀) := (isIntegral_algHom_iff f e.injective).1 h
  obtain ⟨c, hc⟩ := IsIntegrallyClosed.isIntegral_iff.1 (h'.tower_top (A := R))
  refine ⟨(↑hN.unit⁻¹ : R) ^ m * c, ?_⟩
  have hu : algebraMap R (FractionRing R) (↑hN.unit⁻¹ : R) * (N : FractionRing R) = 1 := by
    rw [← map_natCast (algebraMap R (FractionRing R)) N, ← map_mul, hN.val_inv_mul, map_one]
  rw [map_mul, map_pow, hc, ← mul_assoc, ← mul_pow, hu, one_pow, one_mul]
end GlobalTheory.BigOn.Exp
