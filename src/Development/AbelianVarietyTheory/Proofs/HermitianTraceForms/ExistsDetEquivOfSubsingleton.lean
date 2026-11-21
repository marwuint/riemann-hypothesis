import Mathlib
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.MemHomogIffIsHomogeneous

open TensorProduct Module Function

namespace GlobalTheory
namespace TopExt

variable {R F H L : Type*} [CommRing R] [AddCommGroup F] [Module R F] [AddCommGroup H] [Module R H]
  [AddCommGroup L] [Module R L]

variable (R H) in

noncomputable def wedgeMul (a b : ℕ) : (⋀[R]^a H) ⊗[R] (⋀[R]^b H) →ₗ[R] ⋀[R]^(a + b) H :=
  LinearMap.codRestrict _
    (LinearMap.mul' R (ExteriorAlgebra R H) ∘ₗ
      TensorProduct.map (⋀[R]^a H).subtype (⋀[R]^b H).subtype) fun t => by
    induction t using TensorProduct.induction_on with
    | zero => simp
    | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
    | tmul x y =>
      simp only [LinearMap.comp_apply, TensorProduct.map_tmul, LinearMap.mul'_apply,
        ExteriorAlgebra.exteriorPower, pow_add]
      exact Submodule.mul_mem_mul x.2 y.2

@[simp] theorem coe_wedgeMul_tmul {a b : ℕ} (x : ⋀[R]^a H) (y : ⋀[R]^b H) :
    (wedgeMul R H a b (x ⊗ₜ y) : ExteriorAlgebra R H) = (x : ExteriorAlgebra R H) * y := rfl

theorem coe_map (n : ℕ) (i : F →ₗ[R] H) (x : ⋀[R]^n F) :
    (exteriorPower.map n i x : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) := by
  have : (⋀[R]^n H).subtype ∘ₗ exteriorPower.map n i =
      (ExteriorAlgebra.map i).toLinearMap ∘ₗ (⋀[R]^n F).subtype := by
    apply exteriorPower.linearMap_ext
    ext v
    simp
  exact LinearMap.congr_fun this x

noncomputable def wedgeMap (i : F →ₗ[R] H) (s : L →ₗ[R] H) (a b : ℕ) :
    (⋀[R]^a F) ⊗[R] (⋀[R]^b L) →ₗ[R] ⋀[R]^(a + b) H :=
  wedgeMul R H a b ∘ₗ TensorProduct.map (exteriorPower.map a i) (exteriorPower.map b s)

theorem coe_wedgeMap_tmul (i : F →ₗ[R] H) (s : L →ₗ[R] H) {a b : ℕ} (x : ⋀[R]^a F)
    (y : ⋀[R]^b L) : (wedgeMap i s a b (x ⊗ₜ y) : ExteriorAlgebra R H) =
      ExteriorAlgebra.map i (x : ExteriorAlgebra R F) *
        ExteriorAlgebra.map s (y : ExteriorAlgebra R L) := by
  simp [wedgeMap, coe_map]

theorem range_pow_eq_map (i : F →ₗ[R] H) (n : ℕ) :
    LinearMap.range (ExteriorAlgebra.ι R ∘ₗ i) ^ n =
      (⋀[R]^n F).map (ExteriorAlgebra.map i).toLinearMap := by
  rw [ExteriorAlgebra.exteriorPower, Submodule.map_pow, ← LinearMap.range_comp,
    ExteriorAlgebra.map_comp_ι]

section Dual

theorem pairingDual_map_dualMap (φ : F →ₗ[R] H) (n : ℕ) (ξ : ⋀[R]^n (Dual R H)) :
    exteriorPower.pairingDual R F n (exteriorPower.map n φ.dualMap ξ) =
      (exteriorPower.map n φ).dualMap (exteriorPower.pairingDual R H n ξ) := by
  have : exteriorPower.pairingDual R F n ∘ₗ exteriorPower.map n φ.dualMap =
      (exteriorPower.map n φ).dualMap ∘ₗ exteriorPower.pairingDual R H n := by
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun f => ?_
    apply exteriorPower.linearMap_ext
    refine AlternatingMap.ext fun v => ?_
    simp
  exact LinearMap.congr_fun this ξ

theorem pairingDual_bijective_of_basis {κ : Type*} [Finite κ] [LinearOrder κ] (b : Basis κ R F)
    (n : ℕ) : Bijective (exteriorPower.pairingDual R F n) := by
  classical
  have : exteriorPower.pairingDual R F n =
      ((b.dualBasis.exteriorPower n).equiv (b.exteriorPower n).dualBasis (Equiv.refl _)).toLinearMap := by
    refine (b.dualBasis.exteriorPower n).ext fun s => ?_
    rw [LinearEquiv.coe_coe, Basis.equiv_apply, Equiv.refl_apply, Basis.coe_dualBasis,
      exteriorPower.basis_coord, exteriorPower.basis_apply, Basis.coe_dualBasis]
    rfl
  rw [this]
  exact LinearEquiv.bijective _

variable (R F) in

theorem pairingDual_bijective [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    Bijective (exteriorPower.pairingDual R F n) := by
  obtain ⟨k, f, g, -, -, hfg⟩ := Module.Finite.exists_comp_eq_id_of_projective R F
  have hb := pairingDual_bijective_of_basis (Pi.basisFun R (Fin k)) n
  have h₁ : ∀ ξ : ⋀[R]^n (Dual R F),
      exteriorPower.map n g.dualMap (exteriorPower.map n f.dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, LinearMap.dualMap_comp_dualMap, hfg,
      LinearMap.dualMap_id, exteriorPower.map_id, LinearMap.id_apply]
  have h₂ : ∀ ξ : Dual R (⋀[R]^n F),
      (exteriorPower.map n g).dualMap ((exteriorPower.map n f).dualMap ξ) = ξ := fun ξ => by
    rw [← LinearMap.comp_apply, LinearMap.dualMap_comp_dualMap, ← exteriorPower.map_comp, hfg,
      exteriorPower.map_id, LinearMap.dualMap_id, LinearMap.id_apply]
  constructor
  · intro x y hxy
    rw [← h₁ x, ← h₁ y]
    congr 1
    apply hb.1
    rw [pairingDual_map_dualMap, pairingDual_map_dualMap, hxy]
  · intro ξ
    obtain ⟨x, hx⟩ := hb.2 ((exteriorPower.map n f).dualMap ξ)
    exact ⟨exteriorPower.map n g.dualMap x, by rw [pairingDual_map_dualMap, hx, h₂]⟩

variable (R F) in

noncomputable def dualEquiv [Module.Finite R F] [Module.Projective R F] (n : ℕ) :
    (⋀[R]^n (Dual R F)) ≃ₗ[R] Dual R (⋀[R]^n F) :=
  LinearEquiv.ofBijective _ (pairingDual_bijective R F n)

@[simp] theorem dualEquiv_apply [Module.Finite R F] [Module.Projective R F] (n : ℕ)
    (ξ : ⋀[R]^n (Dual R F)) : dualEquiv R F n ξ = exteriorPower.pairingDual R F n ξ := rfl

variable (F) in

theorem rankAtStalk_dual [Module.Finite R F] [Module.Projective R F] (p : PrimeSpectrum R) :
    rankAtStalk (Dual R F) p = rankAtStalk F p := by
  let S := p.asIdeal.primeCompl
  have h₁ := LocalizedModule.isBaseChange S F
  have h₂ := LocalizedModule.isBaseChange S (Dual R F)
  have : Module.Free (Localization S) (LocalizedModule S F) :=
    Module.free_of_flat_of_isLocalRing
  have e := h₂.equiv.symm ≪≫ₗ (SymAlg.isBaseChange_dual h₁).equiv
  exact e.finrank_eq.trans (Module.finrank_linearMap_self _ _ _)

end Dual

end TopExt
end GlobalTheory
