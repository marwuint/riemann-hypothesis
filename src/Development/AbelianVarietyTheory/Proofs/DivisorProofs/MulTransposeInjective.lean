import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open GlobalTheory.Doubling (absE)

noncomputable section

namespace GlobalTheory.MixedLagr

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

def hat {κ : Type} (w : (κ → F) × (κ → F)) : (κ → AF F) × (κ → AF F) :=
  (fun i => algebraMap F (AF F) (w.1 i), fun i => algebraMap F (AF F) (w.2 i))

theorem hat_add {κ : Type} (a b : (κ → F) × (κ → F)) : hat (a + b) = hat a + hat b := by
  simp only [hat, Prod.fst_add, Prod.snd_add, Pi.add_apply, map_add]; rfl

theorem hat_smul {κ : Type} (c : F) (a : (κ → F) × (κ → F)) : hat (c • a) = algebraMap F (AF F) c • hat a := by
  simp only [hat, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_mul]; rfl

theorem hat_zero {κ : Type} : hat (0 : (κ → F) × (κ → F)) = 0 := by
  simp only [hat, Prod.fst_zero, Prod.snd_zero, Pi.zero_apply, map_zero]; rfl

theorem schr_comp {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {κ : Type} [Fintype κ]
    (w w' : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    schr ψ w (schr ψ w' φ) = ψ (⅟(2 : R) * (w.1 ⬝ᵥ w'.2 - w'.1 ⬝ᵥ w.2)) • schr ψ (w + w') φ := by
  funext x
  simp only [schr, Pi.smul_apply, smul_eq_mul, ← mul_assoc, ← AddChar.map_add_eq_mul, Prod.fst_add, Prod.snd_add,
    add_assoc, add_dotProduct, dotProduct_add]
  congr 2
  linear_combination (-(w.1 ⬝ᵥ w'.2)) * invOf_mul_self (2 : R)

variable {n d d₁ : ℕ} {X : Spc F E n} {W : Spc F E d} {W₁ : Spc F E d₁}

def IsMixed (M₁ : Model σ X W₁) (H' : Plane E d d₁) (m : Matrix (Fin n) (Fin d) (AE F E)) : Prop :=
  ∃ u ∈ (iso0 n H' : Set (Matrix (Fin n) (Fin d) (AE F E))), ∃ z : Matrix (Fin n) (Fin d₁) (AE F E),
    (M₁.co.e z).1 = 0 ∧ m = u + incM F (1 : Matrix (Fin n) (Fin n) E) * z * (incM F H'.ι)ᵀ

theorem isMixed_zero (M₁ : Model σ X W₁) (H' : Plane E d d₁) : IsMixed M₁ H' 0 :=
  ⟨0, ⟨0, by ext i j; simp [Matrix.vecMulVec_apply]⟩, 0, by simp, by simp⟩

theorem IsMixed.add {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m m' : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H' m) (h' : IsMixed M₁ H' m') : IsMixed M₁ H' (m + m') := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  obtain ⟨u', ⟨y', rfl⟩, z', hz', rfl⟩ := h'
  refine ⟨Matrix.vecMulVec (y + y') (incV F H'.x), ⟨y + y', rfl⟩, z + z', by simp [hz, hz'], ?_⟩
  rw [Matrix.add_vecMulVec, Matrix.mul_add, Matrix.add_mul]
  abel

theorem IsMixed.smul {M₁ : Model σ X W₁} {H' : Plane E d d₁} {m : Matrix (Fin n) (Fin d) (AE F E)}
    (h : IsMixed M₁ H' m) (t : AF F) : IsMixed M₁ H' (t • m) := by
  obtain ⟨u, ⟨y, rfl⟩, z, hz, rfl⟩ := h
  refine ⟨Matrix.vecMulVec (t • y) (incV F H'.x), ⟨t • y, rfl⟩, t • z, by simp [hz], ?_⟩
  rw [smul_add, Matrix.smul_vecMulVec, Matrix.mul_smul, Matrix.smul_mul]

def lagr (M : Model σ X W) (M₁ : Model σ X W₁) (H' : Plane E d d₁) :
    Submodule F ((Fin n × Fin d → F) × (Fin n × Fin d → F)) where
  carrier := {w | IsMixed M₁ H' (M.co.e.symm (hat w))}
  zero_mem' := by simpa [hat_zero] using isMixed_zero M₁ H'
  add_mem' := fun ha hb => by simpa [Set.mem_setOf_eq, hat_add, map_add] using ha.add hb
  smul_mem' := fun c a ha => by
    show IsMixed M₁ H' (M.co.e.symm (hat (c • a)))
    rw [hat_smul, LinearEquiv.map_smul]
    exact ha.smul _

end GlobalTheory.MixedLagr

end
