import Mathlib
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.ContDiffOnExpPartialHomeomorphSymm

namespace CompanionTheory.D.Upq

open Matrix
open scoped Matrix.Norms.L2Operator MatrixOrder ComplexOrder

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

theorem posDef_conjTranspose_mul_self_GL (g : GL n 𝕜) : ((g : Matrix n n 𝕜)ᴴ * g).PosDef :=
  PosDef.conjTranspose_mul_self _ (mulVec_injective_of_isUnit g.isUnit)

noncomputable def polarPos (g : GL n 𝕜) : Matrix n n 𝕜 := CFC.sqrt ((g : Matrix n n 𝕜)ᴴ * g)

theorem polarPos_posDef (g : GL n 𝕜) : (polarPos g).PosDef := by
  have h := posDef_conjTranspose_mul_self_GL g
  rw [← isStrictlyPositive_iff_posDef] at h ⊢
  exact IsStrictlyPositive.sqrt _ h

theorem polarPos_mul_self (g : GL n 𝕜) : polarPos g * polarPos g = (g : Matrix n n 𝕜)ᴴ * g :=
  CFC.sqrt_mul_sqrt_self _ ((posDef_conjTranspose_mul_self_GL g).posSemidef.nonneg)

noncomputable def polarUnitary (g : GL n 𝕜) : Matrix n n 𝕜 := (g : Matrix n n 𝕜) * (polarPos g)⁻¹

theorem isUnit_det_of_posDef {p : Matrix n n 𝕜} (hp : p.PosDef) : IsUnit p.det :=
  (isUnit_iff_isUnit_det p).1 hp.isUnit

theorem polarUnitary_mem (g : GL n 𝕜) : polarUnitary g ∈ unitaryGroup n 𝕜 := by
  rw [mem_unitaryGroup_iff']
  have hP : (polarPos g)ᴴ = polarPos g := (polarPos_posDef g).isHermitian
  have hd := isUnit_det_of_posDef (polarPos_posDef g)
  rw [star_eq_conjTranspose, polarUnitary, conjTranspose_mul, conjTranspose_nonsing_inv, hP]
  calc (polarPos g)⁻¹ * (g : Matrix n n 𝕜)ᴴ * ((g : Matrix n n 𝕜) * (polarPos g)⁻¹)
      = (polarPos g)⁻¹ * ((g : Matrix n n 𝕜)ᴴ * g) * (polarPos g)⁻¹ := by
        simp only [Matrix.mul_assoc]
    _ = (polarPos g)⁻¹ * (polarPos g * polarPos g) * (polarPos g)⁻¹ := by rw [polarPos_mul_self]
    _ = 1 := by
        rw [← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ hd, Matrix.one_mul,
          Matrix.mul_nonsing_inv _ hd]

theorem polarUnitary_mul_polarPos (g : GL n 𝕜) : polarUnitary g * polarPos g = g := by
  rw [polarUnitary, Matrix.mul_assoc,
    Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef (polarPos_posDef g)), Matrix.mul_one]

theorem polar_unique {g : GL n 𝕜} {k p : Matrix n n 𝕜} (hk : k ∈ unitaryGroup n 𝕜)
    (hp : p.PosDef) (h : k * p = g) : polarPos g = p ∧ polarUnitary g = k := by
  have hkk : kᴴ * k = 1 := by rw [← star_eq_conjTranspose]; exact mem_unitaryGroup_iff'.1 hk
  have hP : pᴴ = p := hp.isHermitian
  have hpp : p * p = (g : Matrix n n 𝕜)ᴴ * g := by
    rw [← h, conjTranspose_mul, hP]
    calc p * p = p * (kᴴ * k) * p := by rw [hkk, Matrix.mul_one]
      _ = p * kᴴ * (k * p) := by simp only [Matrix.mul_assoc]
  have h1 : polarPos g = p := CFC.sqrt_unique hpp hp.posSemidef.nonneg
  refine ⟨h1, ?_⟩
  rw [polarUnitary, h1, ← h, Matrix.mul_assoc,
    Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef hp), Matrix.mul_one]

noncomputable def polarMul (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) : GL n 𝕜 :=
    ⟨kp.1 * kp.2, kp.2.1⁻¹ * star (kp.1 : Matrix n n 𝕜), by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (kp.2 : Matrix n n 𝕜),
        Matrix.mul_nonsing_inv _ (isUnit_det_of_posDef kp.2.2), Matrix.one_mul]
      exact mem_unitaryGroup_iff.1 kp.1.2, by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (star (kp.1 : Matrix n n 𝕜)),
        mem_unitaryGroup_iff'.1 kp.1.2, Matrix.one_mul,
        Matrix.nonsing_inv_mul _ (isUnit_det_of_posDef kp.2.2)]⟩

noncomputable def polarEquiv : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef} ≃ GL n 𝕜 where
  toFun := polarMul
  invFun g := (⟨polarUnitary g, polarUnitary_mem g⟩, ⟨polarPos g, polarPos_posDef g⟩)
  left_inv kp := by
    obtain ⟨⟨k, hk⟩, ⟨p, hp⟩⟩ := kp
    have := polar_unique (g := polarMul (⟨k, hk⟩, ⟨p, hp⟩)) hk hp rfl
    exact Prod.ext (Subtype.ext this.2) (Subtype.ext this.1)
  right_inv g := Units.ext (polarUnitary_mul_polarPos g)

@[simp] theorem coe_polarEquiv_apply (kp : unitaryGroup n 𝕜 × {p : Matrix n n 𝕜 // p.PosDef}) :
    ((polarEquiv kp : GL n 𝕜) : Matrix n n 𝕜) = kp.1 * kp.2 := rfl

end CompanionTheory.D.Upq
