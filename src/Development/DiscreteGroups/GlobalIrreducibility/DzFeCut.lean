import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.DzLcFin
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo

noncomputable section

open GlobalTheory.GLq GlobalTheory.Whittaker GlobalTheory.SmGL Matrix

namespace DiscreteGroups.sglob.DzFe

theorem cycM_mul_tr (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  obtain ⟨l, rfl⟩ := (finRotate n).surjective i
  rw [Finset.sum_eq_single l]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
  · intro b _ hb
    have : ¬ finRotate n l = finRotate n b := fun h => hb ((finRotate n).injective h).symm
    rw [Matrix.of_apply, Matrix.of_apply, if_neg this, zero_mul]
  · simp

theorem tr_mul_cycM (g n : ℕ) :
    (Matrix.of fun i k : Fin n => if finRotate n i = k then (1 : ZMod g) else 0) *
      (Matrix.of fun i k : Fin n => if i = finRotate n k then (1 : ZMod g) else 0) = 1 := by
  ext i k
  rw [Matrix.mul_apply, Matrix.one_apply]
  rw [Finset.sum_eq_single (finRotate n i)]
  · rw [Matrix.of_apply, Matrix.of_apply, if_pos rfl, one_mul]
    by_cases h : i = k
    · subst h; simp
    · rw [if_neg h, if_neg (fun e => h ((finRotate n).injective e))]
  · intro b _ hb
    rw [Matrix.of_apply, Matrix.of_apply, if_neg (Ne.symm hb), zero_mul]
  · simp

def cyc (g n : ℕ) : GL (Fin n) (ZMod g) :=
  ⟨Matrix.of fun i k => if i = finRotate n k then 1 else 0, Matrix.of fun i k => if finRotate n i = k then 1 else 0,
    cycM_mul_tr g n, tr_mul_cycM g n⟩

end DiscreteGroups.sglob.DzFe
