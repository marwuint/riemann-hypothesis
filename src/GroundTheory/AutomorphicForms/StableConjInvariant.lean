import Mathlib
import GroundTheory.AutomorphicForms.StableConjTorus

namespace GroundTheory.Automorphic

open Module

theorem mul_comm_of_mul_inv_comm {G : Type*} [Group G] {a x : G} (hx : x * a⁻¹ = a⁻¹ * x) :
    a * x = x * a := by
  calc a * x = a * (x * a⁻¹) * a := by group
    _ = a * (a⁻¹ * x) * a := by rw [hx]
    _ = x * a := by group

variable {F E : Type*} [Field F] [Field E] [Algebra F E] [Algebra.IsQuadraticExtension F E]
variable {V : Type*} [AddCommGroup V] [Module E V] [FiniteDimensional E V]

namespace HermitianForm

variable (h : HermitianForm F E V)

omit [FiniteDimensional E V] in

theorem adjointEquiv_mem_torusE {γ t : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup)
    (ht : t ∈ torusE γ) : h.adjointEquiv t ∈ torusE γ := by
  rw [mem_torusE] at *
  have h1 := congrArg h.adjointEquiv ht
  rw [adjointEquiv_mul, adjointEquiv_mul, (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ] at h1
  exact mul_comm_of_mul_inv_comm h1

omit [FiniteDimensional E V] in

theorem conj_mem_unitaryGroup_iff {γ : V ≃ₗ[E] V} (hγ : γ ∈ h.unitaryGroup) (g : V ≃ₗ[E] V) :
    g * γ * g⁻¹ ∈ h.unitaryGroup ↔ h.adjointEquiv g * g ∈ torusE γ := by
  have hγ' := (h.mem_unitaryGroup_iff_adjointEquiv γ).1 hγ
  rw [mem_unitaryGroup_iff_adjointEquiv_mul, mem_torusE, adjointEquiv_mul, adjointEquiv_mul,
    adjointEquiv_inv, hγ']
  set A := h.adjointEquiv g
  constructor
  · intro hX
    calc γ * (A * g) = γ * A * ((A⁻¹ * (γ⁻¹ * A)) * (g * γ * g⁻¹)) * g := by rw [hX]; group
      _ = A * g * γ := by group
  · intro hc
    calc A⁻¹ * (γ⁻¹ * A) * (g * γ * g⁻¹) = A⁻¹ * γ⁻¹ * ((A * g) * γ) * g⁻¹ := by group
      _ = A⁻¹ * γ⁻¹ * (γ * (A * g)) * g⁻¹ := by rw [hc]
      _ = 1 := by group

variable (γ : h.unitaryGroup) [Fact (IsRegularSemisimple (γ : V ≃ₗ[E] V))]

noncomputable def torusStar : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) where
  toFun t := TorusE.mk (h.adjointEquiv t.val) (h.adjointEquiv_mem_torusE γ.2 t.val_mem)
  map_one' := TorusE.ext (by simp [adjointEquiv_one])
  map_mul' a b := by
    rw [mul_comm a b]
    exact TorusE.ext (by simp [adjointEquiv_mul])

@[simp] theorem val_torusStar (t : TorusE (γ : V ≃ₗ[E] V)) :
    (h.torusStar γ t).val = h.adjointEquiv t.val := rfl

noncomputable def torusNorm : TorusE (γ : V ≃ₗ[E] V) →* TorusE (γ : V ≃ₗ[E] V) :=
  h.torusStar γ * MonoidHom.id _

theorem torusNorm_apply (t : TorusE (γ : V ≃ₗ[E] V)) : h.torusNorm γ t = h.torusStar γ t * t :=
  rfl

noncomputable def selfAdjointTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  MonoidHom.eqLocus (h.torusStar γ) (MonoidHom.id _)

theorem mem_selfAdjointTorus {c : TorusE (γ : V ≃ₗ[E] V)} :
    c ∈ h.selfAdjointTorus γ ↔ h.torusStar γ c = c := Iff.rfl

noncomputable def normTorus : Subgroup (TorusE (γ : V ≃ₗ[E] V)) :=
  (h.torusNorm γ).range

abbrev centralizerTorusFirstCohomology := h.selfAdjointTorus γ ⧸ (h.normTorus γ).subgroupOf (h.selfAdjointTorus γ)

theorem mk_eq_mk_iff (c c' : h.selfAdjointTorus γ) :
    (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' ↔
      ∃ t, (c' : TorusE (γ : V ≃ₗ[E] V)) = c * h.torusNorm γ t := by
  rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [ht]
    simp
  · rintro ⟨t, ht⟩
    refine ⟨t, ?_⟩
    simp [ht]

noncomputable def normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    h.selfAdjointTorus γ :=
  ⟨TorusE.mk (h.adjointEquiv g * g) ((h.conj_mem_unitaryGroup_iff γ.2 g).1 hg),
    TorusE.ext (by simp [adjointEquiv_mul, adjointEquiv_adjointEquiv])⟩

@[simp] theorem val_normOf (g : V ≃ₗ[E] V) (hg : g * γ * g⁻¹ ∈ h.unitaryGroup) :
    (h.normOf γ g hg : TorusE (γ : V ≃ₗ[E] V)).val = h.adjointEquiv g * g := rfl

noncomputable def twistOf (c : h.selfAdjointTorus γ) : HermitianForm F E V :=
  h.twist (c : TorusE (γ : V ≃ₗ[E] V)).val (congrArg TorusE.val c.2)

theorem twistOf_apply (c : h.selfAdjointTorus γ) (x y : V) :
    (h.twistOf γ c).toSesq x y = h.toSesq ((c : TorusE (γ : V ≃ₗ[E] V)).val x) y := rfl

theorem twistOf_isometric_of_mk_eq {c c' : h.selfAdjointTorus γ}
    (hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c') :
    Isometric (h.twistOf γ c) (h.twistOf γ c') := by
  rw [mk_eq_mk_iff] at hcc
  obtain ⟨t, ht⟩ := hcc
  have hc : (c : TorusE (γ : V ≃ₗ[E] V)) * h.torusNorm γ t =
      h.torusStar γ t * c * t := by
    rw [torusNorm_apply]
    simp only [mul_comm, mul_left_comm]
  refine Isometric.symm ⟨t.val, fun x y => ?_⟩
  rw [twistOf_apply, twistOf_apply, ← h.toSesq_adjointEquiv_left t.val, ht, hc]
  rfl

def InKernel (x : h.centralizerTorusFirstCohomology γ) : Prop :=
  Quotient.liftOn' x (fun c => Isometric (h.twistOf γ c) h) fun c c' hr => propext (by
    have hcc : (QuotientGroup.mk c : h.centralizerTorusFirstCohomology γ) = QuotientGroup.mk c' := Quotient.sound hr
    exact ⟨fun H => (h.twistOf_isometric_of_mk_eq γ hcc).symm.trans H,
      fun H => (h.twistOf_isometric_of_mk_eq γ hcc).trans H⟩)

theorem inKernel_mk (c : h.selfAdjointTorus γ) :
    h.InKernel γ (QuotientGroup.mk c) ↔ Isometric (h.twistOf γ c) h := Iff.rfl

end HermitianForm

end GroundTheory.Automorphic
