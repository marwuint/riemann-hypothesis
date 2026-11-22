import Mathlib
import GroundTheory.AutomorphicForms.ArchimedeanWhittaker.ComplexWhittaker.InstMeasurableSpaceU2
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.EqZeroOfForallIntegralCoeff

namespace GroundTheory.Automorphic.ArchWhittakerC

namespace PW

open Matrix MeasureTheory Complex Finset Polynomial

noncomputable def ent (a b : Fin 2) (k : U2) : ℂ := (k : Matrix (Fin 2) (Fin 2) ℂ) a b

noncomputable def detU (k : U2) : ℂ := (k : Matrix (Fin 2) (Fin 2) ℂ).det

theorem continuous_ent (a b : Fin 2) : Continuous (ent a b) :=
  (continuous_apply b).comp ((continuous_apply a).comp continuous_subtype_val)

theorem continuous_detU : Continuous detU :=
  Continuous.matrix_det continuous_subtype_val

theorem detU_ne_zero (k : U2) : detU k ≠ 0 := det_ne_zero_of_U2 k

theorem continuous_detU_zpow (q : ℤ) : Continuous fun k => detU k ^ q :=
  continuous_detU.zpow₀ q fun k => Or.inl (detU_ne_zero k)

noncomputable def mono (α β γ δ : ℕ) (k : U2) : ℂ :=
  ent 0 0 k ^ α * ent 0 1 k ^ β * ent 1 0 k ^ γ * ent 1 1 k ^ δ

theorem continuous_mono (α β γ δ : ℕ) : Continuous (mono α β γ δ) :=
  ((((continuous_ent 0 0).pow α).mul ((continuous_ent 0 1).pow β)).mul
    ((continuous_ent 1 0).pow γ)).mul ((continuous_ent 1 1).pow δ)

variable (g : U2 → ℂ)

variable {g}

theorem star_eq_adjugate (k : U2) :
    star (k : Matrix (Fin 2) (Fin 2) ℂ) = (detU k)⁻¹ • (k : Matrix (Fin 2) (Fin 2) ℂ).adjugate := by
  have h1 : star (k : Matrix (Fin 2) (Fin 2) ℂ) = (k : Matrix (Fin 2) (Fin 2) ℂ)⁻¹ :=
    (Matrix.inv_eq_left_inv (Matrix.UnitaryGroup.star_mul_self k)).symm
  rw [h1, Matrix.inv_def, Ring.inverse_eq_inv']
  rfl

theorem conj_ent (k : U2) :
    (starRingEnd ℂ) (ent 0 0 k) = (detU k)⁻¹ * ent 1 1 k ∧
    (starRingEnd ℂ) (ent 0 1 k) = (detU k)⁻¹ * -ent 1 0 k ∧
    (starRingEnd ℂ) (ent 1 0 k) = (detU k)⁻¹ * -ent 0 1 k ∧
    (starRingEnd ℂ) (ent 1 1 k) = (detU k)⁻¹ * ent 0 0 k := by
  have h := star_eq_adjugate k
  have e : ∀ a b : Fin 2, (starRingEnd ℂ) (ent a b k) =
      ((detU k)⁻¹ • (k : Matrix (Fin 2) (Fin 2) ℂ).adjugate) b a := by
    intro a b
    rw [← h]; rfl
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [e] <;> simp [Matrix.adjugate_fin_two, ent]

theorem conj_detU (k : U2) : (starRingEnd ℂ) (detU k) = (detU k)⁻¹ := by
  have h : (star (k : Matrix (Fin 2) (Fin 2) ℂ)).det = (detU k)⁻¹ := by
    rw [star_eq_adjugate, Matrix.det_smul, Matrix.det_adjugate, Fintype.card_fin]
    have hd := detU_ne_zero k
    simp only [detU] at hd ⊢
    norm_num
    field_simp
  rw [← h, Matrix.star_eq_conjTranspose, Matrix.det_conjTranspose]; rfl

noncomputable def monoDet (α β γ δ : ℕ) (q : ℤ) : C(U2, ℂ) :=
  ⟨fun k => mono α β γ δ k * detU k ^ q, (continuous_mono _ _ _ _).mul (continuous_detU_zpow q)⟩

@[simp] theorem monoDet_apply (α β γ δ : ℕ) (q : ℤ) (k : U2) :
    monoDet α β γ δ q k = mono α β γ δ k * detU k ^ q := rfl

def monoSet : Set C(U2, ℂ) := {f | ∃ (α β γ δ : ℕ) (q : ℤ), f = monoDet α β γ δ q}

theorem monoDet_mul (α β γ δ α' β' γ' δ' : ℕ) (q q' : ℤ) :
    monoDet α β γ δ q * monoDet α' β' γ' δ' q' =
      monoDet (α + α') (β + β') (γ + γ') (δ + δ') (q + q') := by
  ext k
  simp only [ContinuousMap.mul_apply, monoDet_apply, mono, pow_add,
    zpow_add₀ (detU_ne_zero k)]
  ring

theorem star_monoDet (α β γ δ : ℕ) (q : ℤ) :
    star (monoDet α β γ δ q) = ((-1 : ℂ) ^ (β + γ)) •
      monoDet δ γ β α (-((α + β + γ + δ : ℕ) : ℤ) - q) := by
  ext k
  obtain ⟨h00, h01, h10, h11⟩ := conj_ent k
  have hd := detU_ne_zero k
  have hz : detU k ^ (-((α + β + γ + δ : ℕ) : ℤ) - q) =
      (detU k)⁻¹ ^ (α + β + γ + δ) * (detU k)⁻¹ ^ q := by
    rw [zpow_sub₀ hd, _root_.zpow_neg, zpow_natCast, inv_pow, _root_.inv_zpow, div_eq_mul_inv]
  simp only [ContinuousMap.star_apply, monoDet_apply, ContinuousMap.smul_apply, smul_eq_mul, mono,
    star_mul', star_pow, Complex.star_def, h00, h01, h10, h11, map_zpow₀, conj_detU, hz]
  simp only [mul_pow]
  rw [neg_pow (ent 1 0 k), neg_pow (ent 0 1 k)]
  ring

set_option synthInstance.maxHeartbeats 400000 in

noncomputable def monoAlg : StarSubalgebra ℂ C(U2, ℂ) :=
  { (Submodule.span ℂ monoSet).toSubalgebra
      (Submodule.subset_span ⟨0, 0, 0, 0, 0, by ext k; simp [mono]⟩)
      (fun x y hx hy => by
        have hmul := Submodule.mul_mem_mul hx hy
        rw [Submodule.span_mul_span] at hmul
        refine (Submodule.span_le.2 ?_) hmul
        rintro _ ⟨f, ⟨α, β, γ, δ, q, rfl⟩, f', ⟨α', β', γ', δ', q', rfl⟩, rfl⟩
        exact Submodule.subset_span ⟨_, _, _, _, _, monoDet_mul _ _ _ _ _ _ _ _ _ _⟩) with
    star_mem' := by
      intro x hx
      change x ∈ Submodule.span ℂ monoSet at hx
      change star x ∈ Submodule.span ℂ monoSet
      induction hx using Submodule.span_induction with
      | mem f hf =>
        obtain ⟨α, β, γ, δ, q, rfl⟩ := hf
        rw [star_monoDet]
        exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, _, _, _, _, rfl⟩)
      | zero => simp
      | add x y _ _ hx hy => rw [star_add]; exact Submodule.add_mem _ hx hy
      | smul c x _ hx => rw [star_smul]; exact Submodule.smul_mem _ _ hx }

theorem eq_zero_of_forall_integral_coeff {g : U2 → ℂ} (hg : Continuous g)
    (h : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2), ∫ k, ((((l₁ * k * l₂ : U2) : Matrix (Fin 2) (Fin 2) ℂ) 0 0) ^ n *
      ((k : Matrix (Fin 2) (Fin 2) ℂ).det) ^ q * g k) ∂μK = 0) : g = 0 :=
  _root_.UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff hg h

end PW

end GroundTheory.Automorphic.ArchWhittakerC
