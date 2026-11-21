import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.NotIsGenericDetRepTwo
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.ValuationDetOfMemKO

noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.SplitWeil ValuativeRel Matrix

namespace DiscreteGroups.sglob.DzType

section Ring

variable {R : Type} [CommRing R] {m : ℕ}

theorem wRev_sq : (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id * (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id
    = 1 := by
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev i)]
  · simp [Matrix.one_apply]
  · intro l hl
    simp [Matrix.one_apply, Ne.symm hl]

def wRev (R : Type) [CommRing R] (m : ℕ) : GL (Fin m) R :=
  ⟨(1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id, (1 : Matrix (Fin m) (Fin m) R).submatrix Fin.rev id,
    wRev_sq, wRev_sq⟩

theorem wRev_mul_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((wRev R m * M : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j = (M : Matrix (Fin m) (Fin m) R) (Fin.rev i) j := by
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev i)]
  · show (1 : Matrix (Fin m) (Fin m) R) (Fin.rev i) (Fin.rev i) * _ = _
    rw [Matrix.one_apply_eq, one_mul]
  · intro l hl
    simp [wRev, Ne.symm hl]

theorem mul_wRev_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((M * wRev R m : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j = (M : Matrix (Fin m) (Fin m) R) i (Fin.rev j) := by
  rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_single (Fin.rev j)]
  · show _ * (1 : Matrix (Fin m) (Fin m) R) (Fin.rev (Fin.rev j)) j = _
    rw [Fin.rev_rev, Matrix.one_apply_eq, mul_one]
  · intro l hl
    have : Fin.rev l ≠ j := fun h => hl (by rw [← h, Fin.rev_rev])
    simp [wRev, this]

theorem wRev_inv : (wRev R m)⁻¹ = wRev R m := Units.ext rfl

theorem wRev_conj_apply (M : GL (Fin m) R) (i j : Fin m) :
    ((wRev R m * M * wRev R m : GL (Fin m) R) : Matrix (Fin m) (Fin m) R) i j =
      (M : Matrix (Fin m) (Fin m) R) (Fin.rev i) (Fin.rev j) := by
  rw [mul_wRev_apply, wRev_mul_apply]

end Ring

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {m : ℕ}

theorem det_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m)) : (u : Matrix (Fin m) (Fin m) k).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => ((mem_unipB _).1 hu).1 i j hij)]
  simp [((mem_unipB _).1 hu).2]

theorem mem_KO_of_unip {u : GL (Fin m) k} (hu : u ∈ unipB k (Fin m))
    (h : ∀ i j, valuation k ((u : Matrix (Fin m) (Fin m) k) i j) ≤ 1) : u ∈ KO k (Fin m) := by
  rw [GlobalTheory.SplitFlip.mem_KO_iff]
  refine ⟨fun i j => (Valuation.mem_integer_iff _ _).2 (h i j), fun i j => ?_⟩
  have hinv : ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) = (u : Matrix (Fin m) (Fin m) k).adjugate := by
    rw [Matrix.coe_units_inv, Matrix.inv_def, det_unip hu, Ring.inverse_one, one_smul]
  let A : Matrix (Fin m) (Fin m) 𝒪[k] := fun i j => ⟨(u : Matrix (Fin m) (Fin m) k) i j,
    (Valuation.mem_integer_iff _ _).2 (h i j)⟩
  have hA : (algebraMap 𝒪[k] k).mapMatrix A = (u : Matrix (Fin m) (Fin m) k) := by ext i j; rfl
  show ((u⁻¹ : GL (Fin m) k) : Matrix (Fin m) (Fin m) k) i j ∈ 𝒪[k]
  rw [hinv, ← hA, ← RingHom.map_adjugate]
  exact (A.adjugate i j).2

end Local

end DiscreteGroups.sglob.DzType
