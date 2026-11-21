import Mathlib
import GroundTheory.AutomorphicForms.MultiplicityOne.Functional

open MeasureTheory Set Filter Topology Function
open NumberField IsDedekindDomain
open scoped ENNReal Pointwise NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace MultiplicityOne

open Reduction AutomorphicForm RightCosetSpace CuspidalSpectrum FourierWhittaker

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

local notation "Γ₁" => rationalGLOne K n

variable {μ : Measure (normOneGL K n)} [μ.IsHaarMeasure]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable {σ : UnitaryRep (normOneGL K n) H}

variable (μ σ) in

def cuspIntertwiners : Submodule ℂ (H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ)) where
  carrier := {T | T ∈ σ.intertwiners (rightRegularRep Γ₁ μ) ∧ ∀ v, T v ∈ cuspidalL2 μ}
  add_mem' hS hT := ⟨add_mem hS.1 hT.1, fun v => add_mem (hS.2 v) (hT.2 v)⟩
  zero_mem' := ⟨zero_mem _, fun _ => zero_mem _⟩
  smul_mem' c _ hT := ⟨Submodule.smul_mem _ c hT.1, fun v => Submodule.smul_mem _ c (hT.2 v)⟩

theorem cuspIntertwiners_map (T : cuspIntertwiners μ σ) (x : normOneGL K n) (w : H) :
    T.1 (σ x w) = rightRegularRep Γ₁ μ x (T.1 w) :=
  T.2.1 x w

theorem cuspIntertwiners_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v) =
      (rightRegularRep Γ₁ μ).integrated μ (UnitaryRep.ccToL1 μ f) (T.1 v) :=
  congrArg (fun L : H →L[ℂ] Lp ℂ 2 (quotientMeasure Γ₁ μ) => L v)
    (UnitaryRep.comp_integrated_of_mem_intertwiners σ μ T.2.1 (UnitaryRep.ccToL1 μ f))

theorem hasContRep_intertwiner_integrated (T : cuspIntertwiners μ σ)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)) (rconv Γ₁ μ f (T.1 v)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (rconv Γ₁ μ f (T.1 v)))
    (cuspIntertwiners_integrated T f v).symm (hasContRep_rconv μ f (T.1 v))

theorem hasContRep_intertwiner_generator (T : cuspIntertwiners μ σ) (x : normOneGL K n)
    (f : CompactlySupportedContinuousMap (normOneGL K n) ℂ) (v : H) :
    HasContRep μ (T.1 (σ x (σ.integrated μ (UnitaryRep.ccToL1 μ f) v)))
      (fun y => rconv Γ₁ μ f (T.1 v) (y * x)) :=
  Eq.subst (motive := fun φ => HasContRep μ φ (fun y => rconv Γ₁ μ f (T.1 v) (y * x)))
    (cuspIntertwiners_map T x _).symm ((hasContRep_intertwiner_integrated T f v).translate x)

theorem exists_hasContRep (T : cuspIntertwiners μ σ) {w : H} (hw : w ∈ smoothSpan μ σ) :
    ∃ F, HasContRep μ (T.1 w) F := by
  induction hw using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨x, f, v, -, rfl⟩ := hw
    exact ⟨_, hasContRep_intertwiner_generator T x f v⟩
  | zero =>
    exact ⟨0, Eq.subst (motive := fun φ => HasContRep μ φ 0) (map_zero T.1).symm hasContRep_zero⟩
  | add w₁ w₂ _ _ h₁ h₂ =>
    obtain ⟨F₁, h₁⟩ := h₁
    obtain ⟨F₂, h₂⟩ := h₂
    exact ⟨F₁ + F₂, Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
      (map_add T.1 w₁ w₂).symm (h₁.add h₂)⟩
  | smul c w _ h =>
    obtain ⟨F, h⟩ := h
    exact ⟨c • F, Eq.subst (motive := fun φ => HasContRep μ φ (c • F))
      (map_smul T.1 c w).symm (h.smul c)⟩

open Classical in
variable (μ σ) in

def whittakerAt (T : cuspIntertwiners μ σ) (w : H) : ℂ :=
  if h : ∃ F, HasContRep μ (T.1 w) F then whittakerOne h.choose 1 else 0

theorem whittakerAt_eq {T : cuspIntertwiners μ σ} {w : H} {F : normOneGL K n → ℂ}
    (h : HasContRep μ (T.1 w) F) : whittakerAt μ σ T w = whittakerOne F 1 := by
  have hex : ∃ F, HasContRep μ (T.1 w) F := ⟨F, h⟩
  rw [whittakerAt, dif_pos hex, hex.choose_spec.unique h]

def whittakerOf (T : cuspIntertwiners μ σ) : Module.Dual ℂ (smoothSpan μ σ) where
  toFun w := whittakerAt μ σ T w
  map_add' w₁ w₂ := by
    obtain ⟨F₁, h₁⟩ := exists_hasContRep T w₁.2
    obtain ⟨F₂, h₂⟩ := exists_hasContRep T w₂.2
    have h : HasContRep μ (T.1 ((w₁ + w₂ : smoothSpan μ σ) : H)) (F₁ + F₂) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (F₁ + F₂))
        (map_add T.1 (w₁ : H) (w₂ : H)).symm (h₁.add h₂)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerAt_eq h₂, whittakerOne_add h₁.1 h₂.1]
  map_smul' c w := by
    obtain ⟨F, h₁⟩ := exists_hasContRep T w.2
    have h : HasContRep μ (T.1 ((c • w : smoothSpan μ σ) : H)) (c • F) :=
      Eq.subst (motive := fun φ => HasContRep μ φ (c • F)) (map_smul T.1 c (w : H)).symm (h₁.smul c)
    rw [whittakerAt_eq h, whittakerAt_eq h₁, whittakerOne_smul, RingHom.id_apply, smul_eq_mul]

theorem whittakerOf_apply (T : cuspIntertwiners μ σ) (w : smoothSpan μ σ) :
    whittakerOf T w = whittakerAt μ σ T w := rfl

end MultiplicityOne

end

end GroundTheory.Automorphic
