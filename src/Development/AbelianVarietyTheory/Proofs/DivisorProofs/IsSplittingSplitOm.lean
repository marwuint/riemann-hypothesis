import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HilbertNinetyQuotientHomEqIff

noncomputable section

open Matrix
open scoped NNReal Kronecker

namespace GlobalTheory.WeilM

variable {R : Type} [CommRing R]

theorem schr_schr [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ] (w w' : (κ → R) × (κ → R))
    (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, Prod.fst_add, Prod.snd_add]
  rw [← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, add_assoc x w.1 w'.1]
  congr 2
  simp only [add_dotProduct, dotProduct_add]
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * (mul_invOf_self (2 : R))

variable (R) in

def swapA : R × R →ₐ[R] R × R := { (RingEquiv.prodComm : R × R ≃+* R × R).toRingHom with commutes' := fun _ => rfl }

@[simp] theorem swapA_apply (x : R × R) : swapA R x = (x.2, x.1) := rfl

def complexDarboux : Darboux (R := ℝ) (symp (Complex.conjAe : ℂ →ₐ[ℝ] ℂ) Complex.I (1 : Matrix Unit Unit ℂ)
    (1 : Matrix Unit Unit ℂ)) Unit where
  e :=
    { toFun := fun x => (fun _ => 2 * (x () ()).re, fun _ => (x () ()).im)
      invFun := fun v => of fun _ _ => ⟨v.1 () / 2, v.2 ()⟩
      map_add' := fun x y => by ext <;> simp [mul_add]
      map_smul' := fun a x => by ext <;> simp [mul_left_comm]
      left_inv := fun x => by ext; apply Complex.ext <;> simp
      right_inv := fun v => by ext <;> simp [mul_div_cancel₀] }
  form w w' := by
    show _ = (fun _ : Unit => 2 * (w () ()).re) ⬝ᵥ (fun _ => (w' () ()).im) -
      (fun _ : Unit => 2 * (w' () ()).re) ⬝ᵥ (fun _ => (w () ()).im)
    simp [symp, hTens, Algebra.trace_complex_apply, dotProduct]
    ring

variable {α β κ : Type}

def flat (σ : κ ≃ α × β) : Matrix α β R ≃ₗ[R] (κ → R) where
  toFun X k := X (σ k).1 (σ k).2
  invFun u := of fun i j => u (σ.symm (i, j))
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv X := by ext i j; simp
  right_inv u := by ext k; simp

theorem flat_apply (σ : κ ≃ α × β) (X : Matrix α β R) (k : κ) : flat σ X k = X (σ k).1 (σ k).2 := rfl

theorem flat_symm_apply (σ : κ ≃ α × β) (u : κ → R) (i : α) (j : β) : (flat σ).symm u i j = u (σ.symm (i, j)) := rfl

abbrev cmp₁ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.fst R R)

abbrev cmp₂ {m n : Type} (X : Matrix m n (R × R)) : Matrix m n R := X.map (RingHom.snd R R)

variable [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β] [Fintype κ]

omit [DecidableEq α] [DecidableEq β] in
theorem flat_dot (σ : κ ≃ α × β) (X Y : Matrix α β R) : flat σ X ⬝ᵥ flat σ Y = trace (X * Yᵀ) := by
  simp only [dotProduct, flat_apply, trace, diag_apply, mul_apply, transpose_apply]
  rw [← Fintype.sum_prod_type']
  exact Equiv.sum_comp σ (fun p => X p.1 p.2 * Y p.1 p.2)

theorem IsHerm.isUnit_cmp₁ {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) : IsUnit (cmp₁ J).det := by
  have hu := h.2.map (RingHom.fst R R)
  rwa [RingHom.map_det] at hu

theorem IsHerm.snd_eq {J : Matrix α α (R × R)} (h : IsHerm (swapA R) J) (i j : α) : (J i j).2 = (J j i).1 := by
  have hc := congrArg Prod.snd (h.1 i j)
  rw [swapA_apply] at hc
  exact hc.symm

def splitDarboux {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) : Darboux (R := R) (symp (swapA R) (1, -1) JA JB) κ where
  e :=
    { toFun := fun x => (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ))
      invFun := fun v => of fun i j =>
        ((flat σ).symm v.1 i j, ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ : Matrix α β R) i j)
      map_add' := fun x y => by
        rw [Prod.mk_add_mk, ← map_add, ← map_add, ← Matrix.add_mul, ← Matrix.mul_add]; rfl
      map_smul' := fun a x => by
        rw [RingHom.id_apply, Prod.smul_mk, ← map_smul, ← map_smul, ← Matrix.smul_mul, ← Matrix.mul_smul]; rfl
      left_inv := fun x => by
        simp only [LinearEquiv.symm_apply_apply, Matrix.mul_assoc, ← transpose_mul,
          nonsing_inv_mul _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          nonsing_inv_mul_cancel_left _ _ hA.isUnit_cmp₁]
        rfl
      right_inv := fun v => by
        show (flat σ ((flat σ).symm v.1), flat σ (cmp₁ JA * ((cmp₁ JA)⁻¹ * (flat σ).symm v.2 * ((cmp₁ JB)⁻¹)ᵀ) *
          (cmp₁ JB)ᵀ)) = v
        simp only [Matrix.mul_assoc, ← transpose_mul,
          mul_nonsing_inv _ hB.isUnit_cmp₁, transpose_one, Matrix.mul_one,
          mul_nonsing_inv_cancel_left _ _ hA.isUnit_cmp₁, LinearEquiv.apply_symm_apply] }
  form w w' := by
    show _ = flat σ (cmp₁ w) ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w' * (cmp₁ JB)ᵀ) -
      flat σ (cmp₁ w') ⬝ᵥ flat σ (cmp₁ JA * cmp₂ w * (cmp₁ JB)ᵀ)
    have key : ∀ (X Y : Matrix α β R), trace (X * (cmp₁ JA * Y * (cmp₁ JB)ᵀ)ᵀ) =
        ∑ i, ∑ j, ∑ k, ∑ l, X i j * (JA i k).1 * (JB j l).1 * Y k l := by
      intro X Y
      simp only [trace, diag_apply, mul_apply, transpose_apply, Finset.mul_sum, Finset.sum_mul, map_apply,
        RingHom.coe_fst]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => Finset.sum_comm.trans ?_
      exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring
    rw [flat_dot, flat_dot, key, key]
    simp only [symp, hTens, Algebra.trace_prod_apply, Algebra.trace_self_apply, Prod.fst_mul, Prod.snd_mul,
      Prod.fst_sum, Prod.snd_sum, swapA_apply, one_mul, neg_mul, map_apply, RingHom.coe_fst, RingHom.coe_snd,
      hA.snd_eq, hB.snd_eq, sub_eq_add_neg]
    congr 2
    have s4 : ∀ f : α → β → α → β → R, ∑ i, ∑ j, ∑ k, ∑ l, f i j k l = ∑ k, ∑ l, ∑ i, ∑ j, f i j k l := fun f => by
      have := Finset.sum_comm (s := Finset.univ) (t := Finset.univ) (f := fun p q : α × β => f p.1 p.2 q.1 q.2)
      simpa only [Fintype.sum_prod_type] using this
    rw [s4]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ =>
      Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem splitDarboux_e {JA : Matrix α α (R × R)} {JB : Matrix β β (R × R)} (hA : IsHerm (swapA R) JA)
    (hB : IsHerm (swapA R) JB) (σ : κ ≃ α × β) (x : Matrix α β (R × R)) :
    (splitDarboux hA hB σ).e x = (flat σ (cmp₁ x), flat σ (cmp₁ JA * cmp₂ x * (cmp₁ JB)ᵀ)) := rfl

def ugFst (J : Matrix β β (R × R)) : UG (swapA R) J →* GL β R :=
  (GeneralLinearGroup.map (RingHom.fst R R)).comp (UG (swapA R) J).subtype

theorem ugFst_val {J : Matrix β β (R × R)} (h : UG (swapA R) J) :
    (ugFst J h).val = cmp₁ ((h : GL β (R × R)) : Matrix β β (R × R)) := rfl

def substB (σ : κ ≃ α × β) : GL β R →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := LinearMap.funLeft ℂ ℂ fun u => flat σ ((flat σ).symm u * (h⁻¹).valᵀ)
  map_one' := by ext φ u; simp
  map_mul' h h' := by ext φ u; simp [Matrix.mul_assoc]

def splitChar (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (a : ℕ) : Rˣ →* ℂ where
  toFun t := (χ (Units.map (MonoidHom.inl R R) t) : ℂ) * (((m t : ℝ) ^ (-(a : ℝ) / 2) : ℝ) : ℂ)
  map_one' := by simp
  map_mul' s t := by
    simp only [map_mul, Circle.coe_mul, NNReal.coe_mul, Real.mul_rpow (NNReal.coe_nonneg _) (NNReal.coe_nonneg _),
      Complex.ofReal_mul]
    ring

def splitOm (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β) :
    UG (swapA R) J →* Module.End ℂ ((κ → R) → ℂ) where
  toFun h := splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) • substB σ (ugFst J h)
  map_one' := by simp
  map_mul' h h' := by simp only [map_mul, smul_mul_smul_comm]

omit [DecidableEq α] [Fintype κ] in
theorem splitOm_apply (m : Rˣ →* ℝ≥0) (χ : (R × R)ˣ →* Circle) (J : Matrix β β (R × R)) (σ : κ ≃ α × β)
    (h : UG (swapA R) J) (φ : (κ → R) → ℂ) (u : κ → R) :
    splitOm m χ J σ h φ u = splitChar m χ (Fintype.card α) (GeneralLinearGroup.det (ugFst J h)) *
      φ (flat σ ((flat σ).symm u * ((ugFst J h)⁻¹).valᵀ)) := rfl

end GlobalTheory.WeilM

end
