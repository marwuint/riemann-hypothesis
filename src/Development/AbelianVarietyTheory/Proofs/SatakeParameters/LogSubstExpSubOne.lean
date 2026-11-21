import Mathlib
import Formalism.FormalGroupWitt.FormalGroupWittProofs.EqSingleOfDegreeEqOne

noncomputable section

namespace GlobalTheory.SubringSeries

open MvPowerSeries Formalism.FG.InjVAux

variable {K : Type} [Field K] {κ : Type}

def intS (A : Subring K) (κ : Type) : Subring (MvPowerSeries κ K) where
  carrier := {F | ∀ n, coeff n F ∈ A}
  mul_mem' := by
    classical
    intro a b ha hb n
    rw [coeff_mul]
    exact A.sum_mem fun x _ => A.mul_mem (ha _) (hb _)
  one_mem' := by
    classical
    intro n
    rw [coeff_one]
    split_ifs
    exacts [A.one_mem, A.zero_mem]
  add_mem' := fun ha hb n => by rw [map_add]; exact A.add_mem (ha n) (hb n)
  zero_mem' := fun n => by rw [map_zero]; exact A.zero_mem
  neg_mem' := fun ha n => by rw [map_neg]; exact A.neg_mem (ha n)

variable {A : Subring K}

theorem mem_intS {F : MvPowerSeries κ K} : F ∈ intS A κ ↔ ∀ n, coeff n F ∈ A := Iff.rfl

theorem finsum_mem' {ι : Type} {f : ι → K} (h : ∀ i, f i ∈ A) : ∑ᶠ i, f i ∈ A :=
  finsum_induction (fun x => x ∈ A) A.zero_mem (fun _ _ => A.add_mem) h

theorem subst_mem {ι : Type} {a : ι → MvPowerSeries κ K} (ha : HasSubst a) (hA : ∀ i, a i ∈ intS A κ)
    {E : MvPowerSeries ι K} (hE : E ∈ intS A ι) : subst a E ∈ intS A κ := by
  intro n
  rw [coeff_subst ha]
  refine finsum_mem' fun d => ?_
  rw [smul_eq_mul]
  refine A.mul_mem (hE d) (((intS A κ).prod_mem fun i _ => (intS A κ).pow_mem (hA i) _) n)

def frob (p : ℕ) (hp : p ≠ 0) (σ : K →+* K) (κ : Type) : MvPowerSeries κ K →+* MvPowerSeries κ K :=
  (expand p hp : MvPowerSeries κ K →ₐ[K] MvPowerSeries κ K).toRingHom.comp (map σ)

section Frob

variable {p : ℕ} {hp : p ≠ 0} {σ : K →+* K}

theorem frob_apply (F : MvPowerSeries κ K) : frob p hp σ κ F = expand p hp (map σ F) := rfl

end Frob

end GlobalTheory.SubringSeries
