import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PullHlComp
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsContinuousForgetForget
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PullPreservesFiniteLimits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.FiniteMaximalSpectrumOfFiniteOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.PullHXApply

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite IsLocalRing

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Ring

theorem isLocalRing_integralClosure (O Ω : Type) [CommRing O] [HenselianLocalRing O] [Field Ω] [Algebra O Ω] :
    IsLocalRing (integralClosure O Ω) := by
  refine IsLocalRing.of_isUnit_or_isUnit_one_sub_self fun x => ?_
  let S := Algebra.adjoin O {(x : Ω)}
  haveI : Module.Finite O S := Module.Finite.iff_fg.2 (IsIntegral.fg_adjoin_singleton x.2)
  haveI : IsLocalRing S := by
    obtain ⟨q, hq⟩ := Ideal.exists_maximal S
    have e : S ≃+* Localization.AtPrime q := RingEquiv.ofBijective (algebraMap _ _)
      ⟨IsLocalization.injective _ q.primeCompl_le_nonZeroDivisors,
        GlobalTheory.surjective_algebraMap_localization_of_henselian O q⟩
    exact e.symm.isLocalRing
  have hle : S ≤ (integralClosure O Ω) :=
    Algebra.adjoin_le (Set.singleton_subset_iff.2 x.2)
  let f : S →+* integralClosure O Ω := (Subalgebra.inclusion hle).toRingHom
  have hx : f ⟨x, Algebra.self_mem_adjoin_singleton O _⟩ = x := rfl
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self (⟨x, Algebra.self_mem_adjoin_singleton O _⟩ : S) with h | h
  · left; simpa [hx] using h.map f
  · right; simpa [hx] using h.map f

variable (O : Type) [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]

instance : IsLocalRing (integralClosure O Ω) := isLocalRing_integralClosure O Ω

variable {Ω}

def galInt (σ : Ω ≃ₐ[K] Ω) : integralClosure O Ω ≃+* integralClosure O Ω where
  toFun x := ⟨σ x, x.2.map ((σ.restrictScalars O : Ω ≃ₐ[O] Ω) : Ω →ₐ[O] Ω)⟩
  invFun x := ⟨σ.symm x, x.2.map ((σ.symm.restrictScalars O : Ω ≃ₐ[O] Ω) : Ω →ₐ[O] Ω)⟩
  left_inv x := Subtype.ext (σ.symm_apply_apply x.1)
  right_inv x := Subtype.ext (σ.apply_symm_apply x.1)
  map_mul' x y := Subtype.ext (map_mul σ x.1 y.1)
  map_add' x y := Subtype.ext (map_add σ x.1 y.1)

variable {O K}

@[simp] theorem galInt_apply (σ : Ω ≃ₐ[K] Ω) (x : integralClosure O Ω) : ((galInt O K σ x : integralClosure O Ω) : Ω) = σ x := rfl

theorem galInt_mul (σ τ : Ω ≃ₐ[K] Ω) (x : integralClosure O Ω) : galInt O K (σ * τ) x = galInt O K σ (galInt O K τ x) := rfl

theorem galInt_one (x : integralClosure O Ω) : galInt O K (1 : Ω ≃ₐ[K] Ω) x = x := rfl

def galRes (σ : Ω ≃ₐ[K] Ω) : ResidueField (integralClosure O Ω) ≃+* ResidueField (integralClosure O Ω) :=
  ResidueField.mapEquiv (galInt O K σ)

variable (O K Ω)

def inertia : Subgroup (Ω ≃ₐ[K] Ω) where
  carrier := {σ | ∀ x : integralClosure O Ω, residue _ (galInt O K σ x) = residue _ x}
  mul_mem' {σ τ} hσ hτ x := (hσ _).trans (hτ x)
  one_mem' x := rfl
  inv_mem' {σ} hσ x := by
    have h := hσ (galInt O K σ⁻¹ x)
    rw [← galInt_mul, mul_inv_cancel, galInt_one] at h
    exact h.symm

end Ring
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
open GlobalTheory.EtC.Rel

section Adic

variable (l : ℕ) [Fact l.Prime]

abbrev liftMod (k : ℕ) : Module (ULift.{1} ℤ_[l]) (ULift.{1} (ZMod (l ^ k))) :=
  Module.compHom _ ((ULift.ringEquiv.symm : ZMod (l ^ k) ≃+* ULift.{1} (ZMod (l ^ k))).toRingHom.comp
    ((PadicInt.toZModPow k).comp (ULift.ringEquiv : ULift.{1} ℤ_[l] ≃+* ℤ_[l]).toRingHom))

def lamObj (k : ℕ) : ModuleCat.{1} (ULift.{1} ℤ_[l]) := @ModuleCat.of _ _ (ULift.{1} (ZMod (l ^ k))) _ (liftMod l k)

def lam (k : ℕ) : Shv ℤ_[l] := ofRings ℤ_[l] ((Functor.const _).obj (lamObj l k))

instance (X : Scheme.{0}) (L : DerivedCategory (ShvS ℤ_[l] X)) (n : ℤ) : Module ℤ_[l] (HX ℤ_[l] X L n) :=
  Module.compHom _ (ULift.ringEquiv.symm : ℤ_[l] ≃+* ULift.{1} ℤ_[l]).toRingHom

variable {O : Type} [CommRing O] [HenselianLocalRing O] (K : Type) [Field K] [Algebra O K]
  (Ω : Type) [Field Ω] [Algebra K Ω] [Algebra O Ω] [IsScalarTower O K Ω]
  {X : Scheme.{0}} (p : X ⟶ Spec (CommRingCat.of O))

end Adic
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
end GlobalTheory.EtC.Psi

namespace GlobalTheory.EtC.Psi
end GlobalTheory.EtC.Psi
