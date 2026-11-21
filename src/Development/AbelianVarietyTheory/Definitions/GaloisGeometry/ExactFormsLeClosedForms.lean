import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.DifferentiableAtDirD
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary

set_option autoImplicit false

noncomputable section

open ReciprocityTheory.L2DbarEstimates (V)
open scoped ContDiff

namespace GlobalTheory.CxForm.HolAtlas

variable {M M' M'' : Type} [TopologicalSpace M] [TopologicalSpace M'] [TopologicalSpace M''] {n n' n'' : ℕ}
  (A : HolAtlas M n) (A' : HolAtlas M' n') (A'' : HolAtlas M'' n'')

def closedForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0}
  add_mem' ha hb := ⟨A.forms.add_mem ha.1 hb.1, fun x => (ha.2.1 x).add (hb.2.1 x),
    by rw [dExt_add ha.1 hb.1, ha.2.2, hb.2.2, add_zero]⟩
  zero_mem' := ⟨A.forms.zero_mem, fun _ => .zero k, A.dExt_zero⟩
  smul_mem' c _ ha := ⟨A.forms.smul_mem ha.1 c, fun x => (ha.2.1 x).smul c, by rw [dExt_smul c ha.1, ha.2.2, smul_zero]⟩

def exactForms (k : ℕ) : Submodule ℂ A.Fld where
  carrier := {α | A.IsDeg k α ∧ ∃ η, A.IsForm η ∧ α = A.dExt η}
  add_mem' ha hb := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    obtain ⟨h₂, η', hη', rfl⟩ := hb
    exact ⟨fun x => (h₁ x).add (h₂ x), η + η', A.forms.add_mem hη hη', (dExt_add hη hη').symm⟩
  zero_mem' := ⟨fun _ => .zero k, 0, A.forms.zero_mem, A.dExt_zero.symm⟩
  smul_mem' c _ ha := by
    obtain ⟨h₁, η, hη, rfl⟩ := ha
    exact ⟨fun x => (h₁ x).smul c, c • η, A.forms.smul_mem hη c, (dExt_smul c hη).symm⟩

variable {A}

theorem mem_closedForms {k : ℕ} {α : A.Fld} : α ∈ A.closedForms k ↔ A.IsForm α ∧ A.IsDeg k α ∧ A.dExt α = 0 := Iff.rfl

theorem mem_exactForms {k : ℕ} {α : A.Fld} : α ∈ A.exactForms k ↔ A.IsDeg k α ∧ ∃ η, A.IsForm η ∧ α = A.dExt η := Iff.rfl

theorem mem_exactForms_succ {k : ℕ} {α : A.Fld} :
    α ∈ A.exactForms (k + 1) ↔ ∃ η, A.IsForm η ∧ A.IsDeg k η ∧ α = A.dExt η := by
  constructor
  · rintro ⟨h, η, hη, rfl⟩
    exact ⟨A.degFld k η, hη.degFld k, isDeg_degFld k η, (h.degFld_eq.symm.trans (degFld_dExt hη k).1)⟩
  · rintro ⟨η, hη, hk, rfl⟩
    exact ⟨hk.dExt, η, hη, rfl⟩

variable (A) in

theorem exactForms_zero : A.exactForms 0 = ⊥ := by
  refine eq_bot_iff.2 fun α ⟨h, η, hη, e⟩ => ?_
  rw [Submodule.mem_bot, ← h.degFld_eq, e]
  exact (degFld_dExt hη 0).2

variable (A) in

def HSm (k : ℕ) : Type := A.closedForms k ⧸ (A.exactForms k).submoduleOf (A.closedForms k)

instance (k : ℕ) : AddCommGroup (A.HSm k) := inferInstanceAs (AddCommGroup (_ ⧸ _))

instance (k : ℕ) : Module ℂ (A.HSm k) := inferInstanceAs (Module ℂ (_ ⧸ _))

namespace HSm

variable (A) in

def mk (k : ℕ) : A.closedForms k →ₗ[ℂ] A.HSm k := Submodule.mkQ _

theorem mk_surjective (k : ℕ) : Function.Surjective (mk A k) := Submodule.mkQ_surjective _

theorem mk_eq_zero {k : ℕ} (α : A.closedForms k) : mk A k α = 0 ↔ (α : A.Fld) ∈ A.exactForms k :=
  (Submodule.Quotient.mk_eq_zero _).trans Iff.rfl

@[elab_as_elim] theorem induction_on {k : ℕ} {P : A.HSm k → Prop} (c : A.HSm k) (h : ∀ α, P (mk A k α)) : P c := by
  obtain ⟨α, rfl⟩ := mk_surjective k c
  exact h α

variable (A) in

def fil (p k : ℕ) : Submodule ℂ (A.HSm k) where
  carrier := {c | ∃ α : A.closedForms k, A.TypeGe p α ∧ mk A k α = c}
  add_mem' := by
    rintro _ _ ⟨α, hα, rfl⟩ ⟨β, hβ, rfl⟩
    exact ⟨α + β, typeGe_iff.2 fun x => add_mem (typeGe_iff.1 hα x) (typeGe_iff.1 hβ x), map_add _ _ _⟩
  zero_mem' := ⟨0, typeGe_iff.2 fun _ => zero_mem _, map_zero _⟩
  smul_mem' c := by
    rintro _ ⟨α, hα, rfl⟩
    exact ⟨c • α, typeGe_iff.2 fun x => Submodule.smul_mem _ c (typeGe_iff.1 hα x), map_smul _ _ _⟩

theorem mem_fil {p k : ℕ} {c : A.HSm k} : c ∈ fil A p k ↔ ∃ α : A.closedForms k, A.TypeGe p α ∧ mk A k α = c := Iff.rfl

variable (A) in

theorem fil_zero (k : ℕ) : fil A 0 k = ⊤ :=
  eq_top_iff.2 fun c _ => induction_on c fun α => ⟨α, fun _ _ _ => Nat.zero_le _, rfl⟩

variable (A) in

def mulClosed (k l : ℕ) : A.closedForms k →ₗ[ℂ] A.closedForms l →ₗ[ℂ] A.closedForms (k + l) :=
  LinearMap.mk₂ ℂ (fun α β => ⟨α * β, A.forms.mul_mem α.2.1 β.2.1, α.2.2.1.mul β.2.2.1,
      by rw [dExt_mul α.2.1 β.2.1, α.2.2.2, β.2.2.2, zero_mul, mul_zero, add_zero]⟩)
    (fun _ _ _ => Subtype.ext (add_mul _ _ _)) (fun _ _ _ => Subtype.ext (smul_mul_assoc _ _ _))
    (fun _ _ _ => Subtype.ext (mul_add _ _ _)) (fun _ _ _ => Subtype.ext (mul_smul_comm _ _ _))

theorem exact_mul {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.exactForms k) (hβ : β ∈ A.closedForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  refine ⟨h.mul hβ.2.1, η * β, A.forms.mul_mem hη hβ.1, ?_⟩
  rw [dExt_mul hη hβ.1, hβ.2.2, mul_zero, add_zero]

theorem mul_exact {k l : ℕ} {α β : A.Fld} (hα : α ∈ A.closedForms k) (hβ : β ∈ A.exactForms l) :
    α * β ∈ A.exactForms (k + l) := by
  obtain ⟨h, η, hη, rfl⟩ := hβ
  refine ⟨hα.2.1.mul h, A.parFld α * η, A.forms.mul_mem hα.1.parFld hη, ?_⟩
  rw [dExt_mul hα.1.parFld hη, dExt_parFld hα.1, hα.2.2, map_zero, neg_zero, zero_mul, zero_add]
  exact congrArg (· * _) (funext fun x => (par_par (α x)).symm)

variable (A) in

def cup (k l : ℕ) : A.HSm k →ₗ[ℂ] A.HSm l →ₗ[ℂ] A.HSm (k + l) :=
  LinearMap.liftQ₂ _ _ ((mulClosed A k l).compr₂ (mk A (k + l)))
    (fun α hα => LinearMap.ext fun β => (mk_eq_zero _).2 (exact_mul hα β.2))
    (fun β hβ => LinearMap.ext fun α => (mk_eq_zero _).2 (mul_exact α.2 hβ))

theorem cup_mk {k l : ℕ} (α : A.closedForms k) (β : A.closedForms l) :
    cup A k l (mk A k α) (mk A l β) = mk A (k + l) (mulClosed A k l α β) := rfl

variable {A'}

def pullClosed {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.closedForms k →ₗ[ℂ] A'.closedForms k where
  toFun α := ⟨A.pullback A' f α, α.2.1.pullback hf, α.2.2.1.pullback f,
    by rw [dExt_pullback hf α.2.1, α.2.2.2]; exact map_zero (A.pullbackAlg A' f)⟩
  map_add' α β := Subtype.ext (map_add (A.pullbackAlg A' f) (α : A.Fld) β)
  map_smul' c α := Subtype.ext (map_smul (A.pullbackAlg A' f) c (α : A.Fld))

theorem pullback_exact {f : M' → M} (hf : A.IsHolo A' f) {k : ℕ} {α : A.Fld} (hα : α ∈ A.exactForms k) :
    A.pullback A' f α ∈ A'.exactForms k := by
  obtain ⟨h, η, hη, rfl⟩ := hα
  exact ⟨h.pullback f, A.pullback A' f η, hη.pullback hf, (dExt_pullback hf hη).symm⟩

def pull {f : M' → M} (hf : A.IsHolo A' f) (k : ℕ) : A.HSm k →ₗ[ℂ] A'.HSm k :=
  Submodule.mapQ _ _ (pullClosed hf k) fun α hα => pullback_exact hf hα

theorem pull_mk {f : M' → M} (hf : A.IsHolo A' f) {k : ℕ} (α : A.closedForms k) :
    pull hf k (mk A k α) = mk A' k (pullClosed hf k α) := rfl

end HSm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm.HolAtlas

open GlobalTheory.GoodMetric (coordVec)

theorem hasDeg_zero_dim (α : Alt 0) : HasDeg 0 α := fun S _ =>
  Finset.card_eq_zero.2 (Finset.eq_empty_of_forall_notMem fun a _ => absurd a.2 (by simp))

def pt₀ : (std 0).Pt := ⟨((), 0), Set.mem_univ _⟩

theorem eq_pt₀ (x : (std 0).Pt) : x = pt₀ := Subtype.ext (Prod.ext rfl (Subsingleton.elim _ _))

theorem isForm_std₀ (α : (std 0).Fld) : (std 0).IsForm α := by
  refine ⟨fun i S => contDiffOn_const.congr fun v _ => congrArg (fun w => (bas 0).repr ((std 0).loc α i w) S)
    (Subsingleton.elim v 0), fun x x' _ => ?_⟩
  rw [eq_pt₀ x', eq_pt₀ x, (hasDeg_zero_dim (α pt₀)).eq_algebraMap, AlgHom.commutes]

theorem dExt_std₀ (α : (std 0).Fld) : (std 0).dExt α = 0 :=
  funext fun x => by simp [dExt_apply, opAt]

theorem mem_closedForms_std₀ (α : (std 0).Fld) : α ∈ (std 0).closedForms 0 :=
  ⟨isForm_std₀ α, fun x => hasDeg_zero_dim _, dExt_std₀ α⟩

def evStd₀ : (std 0).closedForms 0 →ₗ[ℂ] ℂ :=
  (bas 0).coord ∅ ∘ₗ LinearMap.proj pt₀ ∘ₗ ((std 0).closedForms 0).subtype

def HSm.std₀Equiv : (std 0).HSm 0 ≃ₗ[ℂ] ℂ := by
  refine LinearEquiv.ofBijective (Submodule.liftQ _ evStd₀ fun α hα => ?_) ⟨?_, fun z => ?_⟩
  · have h : (α : (std 0).Fld) ∈ (std 0).exactForms 0 := hα
    rw [exactForms_zero, Submodule.mem_bot] at h
    simp [evStd₀, h]
  · refine (injective_iff_map_eq_zero _).2 fun c hc => ?_
    induction c using HSm.induction_on with
    | h α =>
      have e : (α : (std 0).Fld) = 0 := funext fun x => by
        rw [eq_pt₀ x, (hasDeg_zero_dim (α.1 pt₀)).eq_algebraMap]
        have : (bas 0).repr (α.1 pt₀) ∅ = 0 := hc
        rw [this, map_zero]; rfl
      rw [show α = 0 from Subtype.ext e]
      exact map_zero _
  · refine ⟨HSm.mk _ 0 ⟨z • 1, mem_closedForms_std₀ _⟩, ?_⟩
    change (bas 0).repr ((z • (1 : (std 0).Fld)) pt₀) ∅ = z
    rw [Pi.smul_apply, Pi.one_apply, ← bas_empty, map_smul, Module.Basis.repr_self]
    simp

theorem HSm.finrank_std₀ : Module.finrank ℂ ((std 0).HSm 0) = 1 :=
  (HSm.std₀Equiv.finrank_eq).trans (Module.finrank_self ℂ)

def zFld : (std 1).Fld := fun x => algebraMap ℂ (Alt 1) (x.crd 0)

theorem dExt_zFld (x : (std 1).Pt) : (std 1).dExt zFld x = dz 0 := by
  have hl : (std 1).loc zFld x.1.1 = fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v • bas 1 ∅ := funext fun v => by
    rw [loc, dif_pos (show v ∈ ((std 1).e x.1.1).target from Set.mem_univ v)]
    unfold zFld
    rw [Algebra.algebraMap_eq_smul_one, bas_empty]
    rfl
  have hd : DifferentiableAt ℂ (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) x.crd :=
    (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ).differentiableAt
  rw [dExt_apply, hl, opAt, opAt, Fin.sum_univ_one, Fin.sum_univ_one,
    coefwise_smul (T := fun f => dirD (Sum.inl 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅,
    coefwise_smul (T := fun f => dirD (Sum.inr 0) f x.crd) (dirD_zero _) (fun v => (EuclideanSpace.proj (0 : Fin 1) : V 1 →L[ℂ] ℂ) v) ∅]
  simp only [Fin.sum_univ_one, dirD, del_eq_fderiv hd, dbar_eq_zero hd, ContinuousLinearMap.fderiv, zero_smul,
    ContinuousLinearMap.zero_apply, mul_zero, add_zero, bas_empty, coordVec]
  simp [dz]

theorem dExt_zFld_ne_zero : (std 1).dExt zFld ≠ 0 := fun h => by
  let x₀ : (std 1).Pt := ⟨(((std 1).cover 0).choose, 0), ((std 1).cover 0).choose_spec⟩
  have e : (0 : Alt 1) = dz 0 := by rw [← dExt_zFld x₀, h]; rfl
  rw [dz, ← bas_singleton] at e
  exact (bas 1).ne_zero _ e.symm

end GlobalTheory.CxForm.HolAtlas

namespace GlobalTheory.CxForm

end GlobalTheory.CxForm

namespace GlobalTheory.CxForm.HolAtlas

end GlobalTheory.CxForm.HolAtlas
