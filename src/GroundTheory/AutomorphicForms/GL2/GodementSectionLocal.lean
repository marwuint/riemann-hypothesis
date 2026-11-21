import Mathlib
import GroundTheory.LocalFields.LocalZeta
import GroundTheory.AutomorphicForms.GLnLocal

open MeasureTheory Matrix Filter Topology
open scoped NNReal ValuativeRel

namespace GroundTheory.Automorphic.GodementSectionLocal

open GroundTheory.LocalField

noncomputable section

set_option linter.unusedSectionVars false

variable {F : Type*} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

variable (F) in

def schwartzBruhat2 : Submodule ℂ ((Fin 2 → F) → ℂ) where
  carrier := {Φ | IsLocallyConstant Φ ∧ HasCompactSupport Φ}
  add_mem' hf hg := ⟨hf.1.add hg.1, hf.2.add hg.2⟩
  zero_mem' := ⟨IsLocallyConstant.const 0, HasCompactSupport.zero⟩
  smul_mem' c _ hf := ⟨hf.1.comp (c • ·), hf.2.smul_left (f := fun _ ↦ c)⟩

theorem mem_schwartzBruhat2 {Φ : (Fin 2 → F) → ℂ} :
    Φ ∈ schwartzBruhat2 F ↔ IsLocallyConstant Φ ∧ HasCompactSupport Φ := Iff.rfl

def slice (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : F → ℂ :=
  fun t ↦ Φ (![0, t] ᵥ* (g : Matrix (Fin 2) (Fin 2) F))

theorem vecMul_zero_cons (t : F) (A : Matrix (Fin 2) (Fin 2) F) :
    ![0, t] ᵥ* A = fun j ↦ t * A 1 j := by
  ext j
  simp [Matrix.vecMul, dotProduct, Fin.sum_univ_two]

def modPow (x : F) (s : ℂ) : ℂ := ((modulus x : ℝ) : ℂ) ^ s

theorem modPow_mul (x y : F) (s : ℂ) : modPow (x * y) s = modPow x s * modPow y s := by
  simp only [modPow, modulus_mul, NNReal.coe_mul, Complex.ofReal_mul]
  exact Complex.mul_cpow_ofReal_nonneg (modulus x).2 (modulus y).2 s

theorem modPow_add {x : F} (hx : x ≠ 0) (s t : ℂ) : modPow x (s + t) = modPow x s * modPow x t :=
  Complex.cpow_add _ _ (Complex.ofReal_ne_zero.2 (by exact_mod_cast modulus_ne_zero hx))

def borelElt (a d : Fˣ) (x : F) : GL (Fin 2) F where
  val := !![(a : F), x; 0, (d : F)]
  inv := !![((a⁻¹ : Fˣ) : F), -(x * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F)); 0, ((d⁻¹ : Fˣ) : F)]
  val_inv := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring
  inv_val := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_inv_eq_inv_val]
    all_goals field_simp
    all_goals ring

theorem borelElt_val (a d : Fˣ) (x : F) :
    (borelElt a d x : Matrix (Fin 2) (Fin 2) F) = !![(a : F), x; 0, (d : F)] := rfl

abbrev detU (g : GL (Fin 2) F) : Fˣ := Matrix.GeneralLinearGroup.det g

def IsSmooth (f : GL (Fin 2) F → ℂ) : Prop :=
  ∃ m : ℕ, ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g

variable [MeasurableSpace F] [BorelSpace F]

theorem localZeta_mul_right (f : F → ℂ) (μ : Fˣ →* ℂˣ) (s : ℂ) (d : Fˣ) :
    localZeta (fun t ↦ f (t * d)) μ s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * localZeta f μ s := by
  set G : Fˣ → ℂ := fun x ↦ f x * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s with hG
  have h1 : modPow (d : F) (-s) * modPow (d : F) s = 1 := by
    rw [← modPow_add d.ne_zero, neg_add_cancel]; simp [modPow]
  have h2 : (((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) = 1 := by
    rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
  have hpt : ∀ x : Fˣ, f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s =
      (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) := by
    intro x
    simp only [hG, Units.val_mul, map_mul, modPow_mul]
    rw [mul_comm (d : F) (x : F)]
    linear_combination (-(f ((x : F) * d) * ((μ x : ℂˣ) : ℂ) * modPow (x : F) s)) *
      ((((μ d)⁻¹ : ℂˣ) : ℂ) * ((μ d : ℂˣ) : ℂ) * h1 + h2)
  have : localZeta (fun t ↦ f (t * d)) μ s =
      ∫ x, (((μ d)⁻¹ : ℂˣ) : ℂ) * modPow (d : F) (-s) * G (d * x) ∂multHaar F :=
    integral_congr_ae (Eventually.of_forall fun x ↦ hpt x)
  rw [this, integral_const_mul, integral_mul_left_eq_self G d]
  rfl

def localSection (χ₁ χ₂ : Fˣ →* ℂˣ) (s : ℂ) (Φ : (Fin 2 → F) → ℂ) (g : GL (Fin 2) F) : ℂ :=
  (χ₁ (detU g) : ℂ) * modPow (detU g : F) s * localZeta (slice Φ g) (χ₁ * χ₂⁻¹) (2 * s)

omit [MeasurableSpace F] [BorelSpace F] in
theorem isLocallyConstant_indicator {X : Type*} [TopologicalSpace X] {S : Set X} (hS : IsClopen S)
    {f : X → ℂ} (hf : IsLocallyConstant f) : IsLocallyConstant (S.indicator f) := by
  rw [IsLocallyConstant.iff_exists_open] at hf ⊢
  intro x
  obtain ⟨V, hV, hxV, hfV⟩ := hf x
  by_cases hx : x ∈ S
  · refine ⟨V ∩ S, hV.inter hS.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_mem hy.2, Set.indicator_of_mem hx, hfV y hy.1]
  · refine ⟨V ∩ Sᶜ, hV.inter hS.compl.isOpen, ⟨hxV, hx⟩, fun y hy ↦ ?_⟩
    rw [Set.indicator_of_notMem hy.2, Set.indicator_of_notMem hx]

variable (F) in

def box (n : ℤ) : AddSubgroup (Fin 2 → F) := AddSubgroup.pi Set.univ fun _ ↦ valBall F n

omit [MeasurableSpace F] [BorelSpace F] in
theorem mem_box {n : ℤ} {x : Fin 2 → F} : x ∈ box F n ↔ ∀ i, x i ∈ valBall F n := by
  simp [box, AddSubgroup.mem_pi]

omit [MeasurableSpace F] [BorelSpace F] in
theorem coe_box (n : ℤ) :
    (box F n : Set (Fin 2 → F)) = Set.pi Set.univ fun _ ↦ (valBall F n : Set F) := by
  ext x
  simp [mem_box]

omit [MeasurableSpace F] [BorelSpace F] in
theorem isClopen_box (n : ℤ) : IsClopen (box F n : Set (Fin 2 → F)) := by
  rw [coe_box]
  exact ⟨isClosed_set_pi fun _ _ ↦ isClosed_valBall n,
    isOpen_set_pi Set.finite_univ fun _ _ ↦ isOpen_valBall n⟩

omit [MeasurableSpace F] [BorelSpace F] in
theorem isCompact_box (n : ℤ) : IsCompact (box F n : Set (Fin 2 → F)) := by
  rw [coe_box]
  exact isCompact_univ_pi fun _ ↦ isCompact_valBall n

omit [MeasurableSpace F] [BorelSpace F] in
theorem ord_nonneg_of_mem_integers {x : F} (hx0 : x ≠ 0) (hx : x ∈ 𝒪[F]) : 0 ≤ ord x :=
  (mem_valBall_iff_le_ord hx0).1 (mem_valBall_zero_iff.2 hx)

omit [MeasurableSpace F] [BorelSpace F] in
theorem det_mem_integers {k : GL (Fin 2) F} (hk : ∀ i j, (k : Matrix (Fin 2) (Fin 2) F) i j ∈ 𝒪[F]) :
    (Matrix.GeneralLinearGroup.det k : F) ∈ 𝒪[F] := by
  rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_fin_two]
  exact sub_mem (mul_mem (hk 0 0) (hk 1 1)) (mul_mem (hk 0 1) (hk 1 0))

omit [MeasurableSpace F] [BorelSpace F] in

theorem ord_det_eq_zero {k : GL (Fin 2) F} (hk : k ∈ GLnLocal.integralGL F 2) :
    ord (detU k : F) = 0 := by
  obtain ⟨hk1, hk2⟩ := (GLnLocal.mem_integralGL_iff F 2).1 hk
  have h1 := ord_nonneg_of_mem_integers (detU k).ne_zero (det_mem_integers hk1)
  have h2 := ord_nonneg_of_mem_integers (detU k⁻¹).ne_zero (det_mem_integers hk2)
  have hinv : detU k⁻¹ = (detU k)⁻¹ := map_inv _ k
  rw [hinv, Units.val_inv_eq_inv_val, ord_inv (detU k).ne_zero] at h2
  omega

omit [MeasurableSpace F] [BorelSpace F] in
theorem IsSmooth.mono {f : GL (Fin 2) F → ℂ} {m : ℕ}
    (hf : ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m, f (g * u) = f g) {m' : ℕ} (h : m ≤ m') :
    ∀ g, ∀ u ∈ GLnLocal.congruenceSubgroup F 2 m', f (g * u) = f g :=
  fun g u hu ↦ hf g u (GLnLocal.congruenceSubgroup_antitone F 2 h hu)

end

end GroundTheory.Automorphic.GodementSectionLocal
