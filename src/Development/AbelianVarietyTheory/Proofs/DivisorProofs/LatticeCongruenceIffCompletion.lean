import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
open NumberField IsDedekindDomain Matrix GlobalTheory.AdLat GlobalTheory.UCls ReciprocityTheory.ChartRestriction.G.FD
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.LocGlob

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ}

theorem ratM_mul (γ δ : Matrix (Fin n) (Fin n) E) : ratM F (γ * δ) = ratM F γ * ratM F δ := by
  have h : ∀ ε : Matrix (Fin n) (Fin n) E,
      ratM F ε = (Algebra.TensorProduct.includeRight : E →ₐ[F] RA F E).toRingHom.mapMatrix ε := by
    intro ε; ext i j; simp [ratM]
  rw [h, h, h, map_mul]

theorem ratM_one : ratM F (1 : Matrix (Fin n) (Fin n) E) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [ratM, Matrix.one_apply, h, Algebra.TensorProduct.one_def]

theorem fv_sub (x y : Fin n → E) : fv F (x - y) = fv F x - fv F y := by
  ext i; simp [fv, TensorProduct.tmul_sub]

theorem fv_nsmul (M : ℕ) (x : Fin n → E) : fv F (M • x) = M • fv F x := by
  ext i
  simp only [fv, Pi.smul_apply]
  exact map_nsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E 1) M (x i)

theorem nsmul_cancel {V : Type} [AddCommGroup V] [Module F V] {M : ℕ} (hM : 1 ≤ M) {u w : V}
    (h : M • u = M • w) : u = w := by
  have h0 : (M : F) ≠ 0 := by exact_mod_cast (by omega : M ≠ 0)
  rw [← Nat.cast_smul_eq_nsmul F, ← Nat.cast_smul_eq_nsmul F] at h
  simpa [h0] using congrArg (fun z => (M : F)⁻¹ • z) h

end GlobalTheory.LocGlob
