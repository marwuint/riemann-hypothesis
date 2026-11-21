import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocallyCompactSpaceOfIsClosed

noncomputable section

open GlobalTheory.Mt.Adelic

namespace GlobalTheory.HkPart

section Fix

variable {E G V : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]

def fix (π : Representation E G V) (K : Subgroup G) : Submodule E V :=
  Representation.invariants (π.comp K.subtype)

variable (π : Representation E G V) {K : Subgroup G}

theorem mem_fix {v : V} : v ∈ fix π K ↔ ∀ k ∈ K, π k v = v :=
  by rw [fix, Representation.mem_invariants]; exact ⟨fun h k hk => h ⟨k, hk⟩, fun h k => h k k.2⟩

theorem apply_eq_of_coset {v : V} (hv : v ∈ fix π K) {x y : G} (h : (x : G ⧸ K) = y) :
    π x v = π y v := by
  rw [QuotientGroup.eq] at h
  rw [show y = x * (x⁻¹ * y) by group, map_mul, Module.End.mul_apply, (mem_fix π).1 hv _ h]

theorem sum_mem_fix {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) {v : V} (hv : v ∈ fix π K) :
    (∑ i, π (z i) v) ∈ fix π K := by
  rw [mem_fix]
  intro k hk
  let F : G ⧸ K → V := fun y => π y.out v
  have hF : ∀ x : G, π x v = F (x : G ⧸ K) := fun x =>
    apply_eq_of_coset π hv (QuotientGroup.out_eq' (x : G ⧸ K)).symm
  rw [map_sum]
  calc ∑ i, π k (π (z i) v) = ∑ i, F ((k * z i : G) : G ⧸ K) := by
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [← Module.End.mul_apply, ← map_mul, hF]
    _ = ∑ i, F ((z i : G) : G ⧸ K) := sum_heckeFam hz F hk
    _ = ∑ i, π (z i) v := Finset.sum_congr rfl fun i _ => (hF _).symm

def op {n : ℕ} {z : Fin n → G} (hz : IsHeckeFam K z) : Module.End E (fix π K) :=
  (∑ i, π (z i)).restrict fun v hv => by
    rw [LinearMap.sum_apply]; exact sum_mem_fix π hz hv

end Fix

section Part

variable {E G V M M' M'' : Type} [Field E] [Group G] [AddCommGroup V] [Module E V]
  [AddCommGroup M] [Module E M] [AddCommGroup M'] [Module E M'] [AddCommGroup M''] [Module E M'']

variable (E) in

abbrev HeckeRel (K : Subgroup G) (M : Type) [AddCommGroup M] [Module E M] : Type :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G), IsHeckeFam K z → Module.End E M → Prop

def part (π : Representation E G V) (K : Subgroup G) (R : HeckeRel E K M) :
    Submodule E (fix π K →ₗ[E] M) where
  carrier := {φ | ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M),
    R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ}
  add_mem' {a b} ha hb n z hz T hT := by
    rw [LinearMap.add_comp, LinearMap.comp_add, ha z hz T hT, hb z hz T hT]
  zero_mem' n z hz T hT := by simp
  smul_mem' c a ha n z hz T hT := by
    rw [LinearMap.smul_comp, LinearMap.comp_smul, ha z hz T hT]

variable {π : Representation E G V} {K : Subgroup G} {R : HeckeRel E K M}

theorem mem_part {φ : fix π K →ₗ[E] M} : φ ∈ part π K R ↔
    ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → φ ∘ₗ op π hz = T ∘ₗ φ :=
  Iff.rfl

def Intertw (R : HeckeRel E K M) (R' : HeckeRel E K M') (f : M →ₗ[E] M') : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T' : Module.End E M'), R' z hz T' →
    ∃ T, R z hz T ∧ f ∘ₗ T = T' ∘ₗ f

variable (π) in

def map {R : HeckeRel E K M} {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) :
    part π K R →ₗ[E] part π K R' where
  toFun φ := ⟨f ∘ₗ (φ : fix π K →ₗ[E] M), fun _ z hz T' hT' => by
    obtain ⟨T, hT, e⟩ := hf z hz T' hT'
    rw [LinearMap.comp_assoc, mem_part.1 φ.2 z hz T hT, ← LinearMap.comp_assoc, e, LinearMap.comp_assoc]⟩
  map_add' a b := Subtype.ext (LinearMap.comp_add _ _ _)
  map_smul' c a := Subtype.ext (LinearMap.comp_smul _ _ _)

@[simp] theorem coe_map {R' : HeckeRel E K M'} (f : M →ₗ[E] M') (hf : Intertw R R' f) (φ : part π K R) :
    ((map π f hf φ : part π K R') : fix π K →ₗ[E] M') = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

def Commutes (R : HeckeRel E K M) (f : Module.End E M) : Prop :=
  ∀ ⦃n : ℕ⦄ (z : Fin n → G) (hz : IsHeckeFam K z) (T : Module.End E M), R z hz T → f ∘ₗ T = T ∘ₗ f

theorem Commutes.intertw {f : Module.End E M} (hf : Commutes R f) : Intertw R R f :=
  fun _ z hz T hT => ⟨T, hT, hf z hz T hT⟩

variable (π) in

def endo (f : Module.End E M) (hf : Commutes R f) : Module.End E (part π K R) :=
  map π f hf.intertw

@[simp] theorem coe_endo (f : Module.End E M) (hf : Commutes R f) (φ : part π K R) :
    ((endo π f hf φ : part π K R) : fix π K →ₗ[E] M) = f ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

variable (π) in

def partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) :
    Representation E Γ (part π K R) where
  toFun γ := endo π (ρ γ) (hρ γ)
  map_one' := by
    ext φ : 1
    exact Subtype.ext (by ext v; simp)
  map_mul' a b := by
    ext φ : 1
    exact Subtype.ext (by simp [LinearMap.comp_assoc]; rfl)

@[simp] theorem coe_partRep {Γ : Type} [Group Γ] (ρ : Representation E Γ M) (hρ : ∀ γ, Commutes R (ρ γ)) (γ : Γ)
    (φ : part π K R) :
    ((partRep π ρ hρ γ φ : part π K R) : fix π K →ₗ[E] M) = ρ γ ∘ₗ (φ : fix π K →ₗ[E] M) := rfl

instance [FiniteDimensional E (fix π K)] [FiniteDimensional E M] : FiniteDimensional E (part π K R) :=
  inferInstance

end Part

section Transport

variable {E' E : Type} [Field E'] [Field E]

def Tr (_ι : E' ≃+* E) (V : Type) : Type := V

variable (ι : E' ≃+* E) {V : Type} [AddCommGroup V] [Module E V]

instance : AddCommGroup (Tr ι V) := inferInstanceAs (AddCommGroup V)

instance : Module E' (Tr ι V) := Module.compHom V (ι : E' →+* E)

def Tr.of : V ≃+ Tr ι V := AddEquiv.refl V

variable {G : Type} [Group G]

end Transport

end GlobalTheory.HkPart
