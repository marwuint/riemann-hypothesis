import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicIndexEquality.Commensurated

noncomputable section

namespace PI.UnitaryGroupMassFormula.AdIndexEq

section Delta

variable {G : Type} [Group G]

def idxRatio (A B : Subgroup G) : ℚ := (B.relIndex A : ℚ) / (A.relIndex B : ℚ)

theorem idxRatio_eq_of_le (A B D : Subgroup G) (hDA : D ≤ A) (hDB : D ≤ B)
    (hA : D.relIndex A ≠ 0) :
    idxRatio A B = (D.relIndex A : ℚ) / (D.relIndex B : ℚ) := by
  have h1 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex A = D.relIndex A :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_left)
  have h2 : D.relIndex (A ⊓ B) * (A ⊓ B).relIndex B = D.relIndex B :=
    Subgroup.relIndex_mul_relIndex (hHK := le_inf hDA hDB) (hKL := inf_le_right)
  rw [Subgroup.inf_relIndex_left] at h1
  rw [Subgroup.inf_relIndex_right] at h2
  have hc0 : D.relIndex (A ⊓ B) ≠ 0 := by
    intro h0
    apply hA
    rw [← h1, h0, zero_mul]
  have hc : (D.relIndex (A ⊓ B) : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hc0
  unfold idxRatio
  rw [← h1, ← h2, Nat.cast_mul, Nat.cast_mul, mul_div_mul_left _ _ hc]

theorem relIndex_inf_three_ne_zero {A B C L : Subgroup G} (hA : A.relIndex L ≠ 0)
    (hB : B.relIndex L ≠ 0) (hC : C.relIndex L ≠ 0) : (A ⊓ B ⊓ C).relIndex L ≠ 0 := by
  exact Subgroup.relIndex_inf_ne_zero (Subgroup.relIndex_inf_ne_zero hA hB) hC

theorem relIndex_self_ne_zero (A : Subgroup G) : A.relIndex A ≠ 0 := by
  rw [Subgroup.relIndex_self]
  exact one_ne_zero

theorem idxRatio_mul (A B C : Subgroup G)
    (hAB : B.relIndex A ≠ 0) (hAC : C.relIndex A ≠ 0) (hBA : A.relIndex B ≠ 0)
    (hBC : C.relIndex B ≠ 0) :
    idxRatio A B * idxRatio B C = idxRatio A C := by
  have hDA := relIndex_inf_three_ne_zero (relIndex_self_ne_zero A) hAB hAC
  have hDB := relIndex_inf_three_ne_zero hBA (relIndex_self_ne_zero B) hBC
  rw [idxRatio_eq_of_le A B (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left)
      (le_trans inf_le_left inf_le_right) hDA,
    idxRatio_eq_of_le B C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_right) inf_le_right hDB,
    idxRatio_eq_of_le A C (A ⊓ B ⊓ C) (le_trans inf_le_left inf_le_left) inf_le_right hDA,
    div_mul_div_comm, mul_comm ((A ⊓ B ⊓ C).relIndex A : ℚ),
    mul_div_mul_left _ _ (Nat.cast_ne_zero.mpr hDB)]

private theorem relIndex_map_of_injective (X Y : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    (X.map f).relIndex (Y.map f) = X.relIndex Y := by
  rw [← Subgroup.relIndex_comap, Subgroup.comap_map_eq_self_of_injective hf]

theorem idxRatio_map (A B : Subgroup G) (f : G →* G) (hf : Function.Injective f) :
    idxRatio (A.map f) (B.map f) = idxRatio A B := by
  unfold idxRatio
  rw [relIndex_map_of_injective _ _ f hf, relIndex_map_of_injective _ _ f hf]

theorem map_conj_mul' (K : Subgroup G) (a b : G) :
    (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom =
      K.map (MulAut.conj (a * b)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [MulAut.conj_apply, mul_assoc]

theorem map_conj_one' (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp [Subgroup.mem_map]

theorem relIndex_conj_conj_ne_zero (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    (K.map (MulAut.conj x).toMonoidHom).relIndex (K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have h1 : K.map (MulAut.conj x).toMonoidHom =
      (K.map (MulAut.conj (y⁻¹ * x)).toMonoidHom).map (MulAut.conj y).toMonoidHom := by
    rw [map_conj_mul', mul_inv_cancel_left]
  rw [h1, relIndex_map_of_injective _ _ _ (by intro a b h; simpa using h)]
  exact hK (y⁻¹ * x)

theorem relIndex_conj_right_ne_zero (K : Subgroup G) (hK : Commensurated K) (a : G) :
    K.relIndex (K.map (MulAut.conj a).toMonoidHom) ≠ 0 := by
  have h := relIndex_conj_conj_ne_zero K hK 1 a
  rwa [map_conj_one'] at h

theorem dIdx_inv_eq (K : Subgroup G) (x : G) :
    dIdx K x⁻¹ = K.relIndex (K.map (MulAut.conj x).toMonoidHom) := by
  unfold dIdx
  rw [← relIndex_map_of_injective _ _ (MulAut.conj x).toMonoidHom (by intro a b h; simpa using h),
    map_conj_mul', mul_inv_cancel, map_conj_one']

theorem modQ_eq_idxRatio (K : Subgroup G) (x : G) :
    modQ K x = idxRatio K (K.map (MulAut.conj x).toMonoidHom) := by
  unfold modQ idxRatio
  rw [dIdx_inv_eq]
  rfl

theorem dIdx_one (K : Subgroup G) : dIdx K 1 = 1 := by
  unfold dIdx
  rw [map_conj_one', Subgroup.relIndex_self]

theorem modQ_one (K : Subgroup G) : modQ K 1 = 1 := by
  unfold modQ
  simp [dIdx_one]

theorem modQ_mul (K : Subgroup G) (hK : Commensurated K) (x y : G) :
    modQ K (x * y) = modQ K x * modQ K y := by
  rw [modQ_eq_idxRatio, modQ_eq_idxRatio, modQ_eq_idxRatio,
    ← idxRatio_map K (K.map (MulAut.conj y).toMonoidHom) (MulAut.conj x).toMonoidHom
      (by intro a b h; simpa using h), map_conj_mul']
  exact (idxRatio_mul K (K.map (MulAut.conj x).toMonoidHom) (K.map (MulAut.conj (x * y)).toMonoidHom)
    (hK x) (hK (x * y)) (relIndex_conj_right_ne_zero K hK x)
    (relIndex_conj_conj_ne_zero K hK (x * y) x)).symm

end Delta

end PI.UnitaryGroupMassFormula.AdIndexEq
