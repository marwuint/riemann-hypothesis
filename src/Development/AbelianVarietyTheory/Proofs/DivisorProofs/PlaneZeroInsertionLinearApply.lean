import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone

noncomputable section

namespace GlobalTheory.ThK.PlaneEv

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

variable {n d d₁ : ℕ}

def idx (hd : d = d₁ + 2) : Fin n × Fin d ≃ Fin n × Fin d₁ ⊕ Fin n × Fin 2 :=
  ((Equiv.refl (Fin n)).prodCongr ((finCongr hd).trans finSumFinEquiv.symm)).trans (Equiv.prodSumDistrib _ _ _)

def ins0 {R : Type} [Zero R] (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → R) : Fin n × Fin d → R :=
  fun k => Sum.elim x 0 (idx hd k)

section Ins

variable {R : Type} (hd : d = d₁ + 2)

@[simp] theorem planeZeroInsertion_apply_inl [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin d₁) :
    ins0 hd x ((idx hd).symm (Sum.inl p)) = x p := by
  simp [ins0]

@[simp] theorem planeZeroInsertion_apply_inr [Zero R] (x : Fin n × Fin d₁ → R) (p : Fin n × Fin 2) :
    ins0 hd x ((idx hd).symm (Sum.inr p)) = 0 := by
  simp [ins0]

theorem ins0_add [AddZeroClass R] (x y : Fin n × Fin d₁ → R) : ins0 hd (x + y) = ins0 hd x + ins0 hd y := by
  funext k; simp only [ins0, Pi.add_apply]; rcases idx hd k with p | p <;> simp

theorem ins0_smul {S : Type} [Zero R] [SMulZeroClass S R] (c : S) (x : Fin n × Fin d₁ → R) :
    ins0 hd (c • x) = c • ins0 hd x := by
  funext k; simp only [ins0, Pi.smul_apply]; rcases idx hd k with p | p <;> simp

end Ins

open scoped Classical

variable (F : Type) [Field F] [NumberField F]

def insertZerosCLM (hd : d = d₁ + 2) :
    (Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) →L[ℝ] (Fin n × Fin d → mixedEmbedding.mixedSpace F) :=
  LinearMap.toContinuousLinearMap
    { toFun := ins0 hd
      map_add' := ins0_add hd
      map_smul' := fun c x => ins0_smul hd c x }

@[simp] theorem planeZeroInsertionLinear_apply (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    insertZerosCLM F hd x = ins0 hd x := rfl

theorem norm_le_ins0 (hd : d = d₁ + 2) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) : ‖x‖ ≤ ‖ins0 hd x‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun p => ?_
  have := norm_le_pi_norm (ins0 hd x) ((idx hd).symm (Sum.inl p))
  rwa [planeZeroInsertion_apply_inl] at this

def ei (hd : d = d₁ + 2) : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d₁) :=
  SchwartzMap.compCLM ℂ (insertZerosCLM F hd).hasTemperateGrowth
    ⟨1, 1, fun x => by
      have := norm_le_ins0 F hd x
      simp only [planeZeroInsertionLinear_apply, pow_one, one_mul]
      linarith [norm_nonneg (ins0 hd x)]⟩

@[simp] theorem ei_apply (hd : d = d₁ + 2) (f : SInf F (Fin n × Fin d)) (x : Fin n × Fin d₁ → mixedEmbedding.mixedSpace F) :
    ei F hd f x = f (ins0 hd x) := rfl

variable {F}

def ev (hd : d = d₁ + 2) (v : Pl F) : ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d₁ → Fv F v) → ℂ :=
  LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem ev_apply (hd : d = d₁ + 2) (v : Pl F) (φ : (Fin n × Fin d → Fv F v) → ℂ) (x : Fin n × Fin d₁ → Fv F v) :
    ev hd v φ x = φ (ins0 hd x) := rfl

variable (F) in

def evA (hd : d = d₁ + 2) : Fn F n d →ₗ[ℂ] Fn F n d₁ := LinearMap.funLeft ℂ ℂ (ins0 hd)

@[simp] theorem evA_apply (hd : d = d₁ + 2) (Φ : Fn F n d) (x : Fin n × Fin d₁ → AF F) : evA F hd Φ x = Φ (ins0 hd x) := rfl

end GlobalTheory.ThK.PlaneEv
