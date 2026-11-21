import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv

noncomputable section

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField GlobalTheory.Published Filter
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.Sa2Prod

section Ring

open Matrix Formalism.UG

variable {R : Type} [CommRing R] {n : Type} [Fintype n] [DecidableEq n]

def trunc (d : R) (A : Matrix n n R) : Matrix n n R := 1 + d • (A - 1)

theorem trunc_one (d : R) : trunc d (1 : Matrix n n R) = 1 := by simp [trunc]

theorem trunc_mul {d : R} (hd : d * d = d) (A B : Matrix n n R) :
    trunc d A * trunc d B = trunc d (A * B) := by
  have h : (d • (A - 1)) * (d • (B - 1)) = d • ((A - 1) * (B - 1)) := by
    rw [Matrix.smul_mul, Matrix.mul_smul, smul_smul, hd]
  unfold trunc
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, h]
  simp only [Matrix.one_mul, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_sub, smul_sub, smul_add]
  abel

theorem cT_trunc (c : R →+* R) {d : R} (hc : c d = d) (A : Matrix n n R) :
    cT c (trunc d A) = trunc d (cT c A) := by
  ext i j
  simp only [cT, trunc, Matrix.transpose_apply, Matrix.map_apply, Matrix.add_apply, Matrix.smul_apply,
    Matrix.sub_apply, smul_eq_mul, map_add, map_mul, map_sub, hc]
  have : ∀ p q : n, c ((1 : Matrix n n R) p q) = (1 : Matrix n n R) q p := by
    intro p q
    by_cases h : p = q
    · subst h; simp
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h)]
  rw [this]

theorem trunc_unitary {d : R} (hd : d * d = d) {X Y J : Matrix n n R} (h : X * J * Y = J) :
    trunc d X * J * trunc d Y = J := by
  have e : trunc d X * J * trunc d Y =
      J + d • (X * J - J + J * Y - J) + (d * d) • ((X - 1) * J * (Y - 1)) := by
    unfold trunc
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul,
      Matrix.mul_smul, Matrix.sub_mul, Matrix.mul_sub, smul_add, smul_sub, smul_smul]
    abel
  rw [e, hd]
  have e2 : (X - 1) * J * (Y - 1) = X * J * Y - X * J - J * Y + J := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul]
    abel
  rw [e2, h, add_assoc, ← smul_add]
  have e3 : X * J - J + J * Y - J + (J - X * J - J * Y + J) = 0 := by abel
  rw [e3, smul_zero, add_zero]

def truncGL {d : R} (hd : d * d = d) (g : GL n R) : GL n R where
  val := trunc d g.val
  inv := trunc d (g⁻¹).val
  val_inv := by rw [trunc_mul hd, Units.mul_inv, trunc_one]
  inv_val := by rw [trunc_mul hd, Units.inv_mul, trunc_one]

end Ring

section Main

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def truncHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {d : AF F}
    (hd : algebraMap (AF F) (AF F ⊗[F] E) d * algebraMap (AF F) (AF F ⊗[F] E) d =
      algebraMap (AF F) (AF F ⊗[F] E) d) (g : HA (AF F) σ J) : HA (AF F) σ J :=
  let g' : HR (AF F) σ J := g
  (⟨truncGL hd g'.1, by
    have h : Formalism.UG.cT (sigR (AF F) σ) (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) * JR (AF F) J *
        (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J := g'.2
    change Formalism.UG.cT (sigR (AF F) σ) (trunc _ (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E))) * JR (AF F) J *
        trunc _ (g'.1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) = JR (AF F) J
    rw [cT_trunc _ (sigR_algebraMap σ d)]
    exact trunc_unitary hd h⟩ : HR (AF F) σ J)

end Main

section Main2

open GlobalTheory.Published.StrongApprox

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem mat_truncHA (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) {d : AF F}
    (hd : algebraMap (AF F) (AF F ⊗[F] E) d * algebraMap (AF F) (AF F ⊗[F] E) d =
      algebraMap (AF F) (AF F ⊗[F] E) d) (g : HA (AF F) σ J) :
    ((HA.mat (AF F) σ J (truncHA σ J hd g)).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) =
      trunc (algebraMap (AF F) (AF F ⊗[F] E) d) (HA.mat (AF F) σ J g).1 := rfl

end Main2

end GlobalTheory.CompanionTheory.Sa2Prod
