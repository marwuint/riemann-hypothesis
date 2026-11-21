import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNsmulFix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntAFSmulMemLatOF
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfTraceMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousPlaceAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompactShellNsmul

open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
open MeasureTheory

namespace GlobalTheory.SplitVacF

end GlobalTheory.SplitVacF

noncomputable section

namespace GlobalTheory.SplitVacF

open GlobalTheory.SplitInvFormF

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
variable {σ : E →ₐ[F] E} {nS nT : ℕ} {JS : Matrix (Fin nS) (Fin nS) E} {JT : Matrix (Fin nT) (Fin nT) E} {xi0 : E}
  {ψ : AddChar (AF F) ℂ}

theorem isSplitIdemF_conj {e : AEF F E} (he : IsSplitIdemF σ e) : IsSplitIdemF σ (cAF σ e) := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  refine ⟨by rw [← map_mul, h1], ?_, v, ε, hpl, ?_⟩
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, mul_comm, h2]
  · rw [cAF_cAF ⟨h1, h2, v, ε, hpl, hsum⟩, add_comm, hsum]

theorem mem_conjHalf_conj {e : AEF F E} (he : IsSplitIdemF σ e) {x : WOF F E nS nT} (hx : ∀ i j, e * x i j = x i j) :
    x ∈ conjHalf σ (cAF σ e) nS nT := fun i j => by rw [cAF_cAF he]; exact hx i j

theorem fin_of_mem {e : AEF F E} (he : IsSplitIdemF σ e) {u : WOF F E nS nT} (hu : u ∈ conjHalf σ e nS nT) :
    u.map (infPartF F E) = 0 := by
  obtain ⟨h1, h2, v, ε, hpl, hsum⟩ := he
  have hs := congrArg (infPartF F E) hsum
  rw [map_add, GlobalTheory.WeilPartsF.infPartF_placeIdem hpl] at hs
  have hc : infPartF F E (cAF σ e) = 0 := by
    have a1 : infPartF F E (cAF σ e) * infPartF F E (cAF σ e) = infPartF F E (cAF σ e) := by
      rw [← map_mul, ← map_mul, h1]
    have a2 : infPartF F E (cAF σ e) * infPartF F E e = 0 := by rw [← map_mul, mul_comm, h2, map_zero]
    linear_combination -a1 - a2 + infPartF F E (cAF σ e) * hs
  ext i j
  show infPartF F E (u i j) = 0
  rw [← hu i j, map_mul, hc, zero_mul]

theorem commF_add_left (u u' y : WOF F E nS nT) :
    commF σ JS JT xi0 ψ (u + u') y = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u' y := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_add_right (u y y' : WOF F E nS nT) :
    commF σ JS JT xi0 ψ u (y + y') = commF σ JS JT xi0 ψ u y * commF σ JS JT xi0 ψ u y' := by
  unfold commF
  rw [← AddChar.map_add_eq_mul, GlobalTheory.HeisThetaF.symplOHF_add_left, GlobalTheory.HeisThetaF.symplOHF_add_right]
  congr 1; ring

theorem commF_zero_left (y : WOF F E nS nT) : commF σ JS JT xi0 ψ 0 y = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_zero_right (u : WOF F E nS nT) : commF σ JS JT xi0 ψ u 0 = 1 := by
  unfold commF
  rw [GlobalTheory.HeisThetaF.symplOHF_zero_left, GlobalTheory.HeisThetaF.symplOHF_zero_right, sub_zero, AddChar.map_zero_eq_one]

theorem commF_neg_right (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ u (-y) * commF σ JS JT xi0 ψ u y = 1 := by
  rw [← commF_add_right, neg_add_cancel, commF_zero_right]

theorem commF_swap (u y : WOF F E nS nT) : commF σ JS JT xi0 ψ y (-u) = commF σ JS JT xi0 ψ u y := by
  unfold commF
  have h1 := GlobalTheory.HeisThetaF.symplOHF_add_right (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) y (-u) u
  have h2 := GlobalTheory.HeisThetaF.symplOHF_add_left (σ := σ) (JS := JS) (JT := JT) (xi0 := xi0) (-u) u y
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_right] at h1
  rw [neg_add_cancel, GlobalTheory.HeisThetaF.symplOHF_zero_left] at h2
  congr 1
  linear_combination -h1 + h2

theorem commF_nsmul_left (u y : WOF F E nS nT) (n : ℕ) :
    commF σ JS JT xi0 ψ (n • u) y = commF σ JS JT xi0 ψ u y ^ n := by
  induction n with
  | zero => rw [zero_smul, commF_zero_left, pow_zero]
  | succ n ih => rw [succ_nsmul, commF_add_left, ih, pow_succ]

theorem commF_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) : commF σ JS JT xi0 ψ x y = 1 := by
  unfold commF
  rw [symplOHF_half he hx hy, symplOHF_half he hy hx, sub_zero, AddChar.map_zero_eq_one]

theorem heisOF_add_half {e : AEF F E} (he : IsSplitIdemF σ e) {x y : WOF F E nS nT} (hx : x ∈ conjHalf σ e nS nT)
    (hy : y ∈ conjHalf σ e nS nT) (f : WOF F E nS nT → ℂ) :
    heisOF σ JS JT xi0 ψ (x + y) f = heisOF σ JS JT xi0 ψ x (heisOF σ JS JT xi0 ψ y f) := by
  rw [heisOF_heisOF, symplOHF_half he hx hy, AddChar.map_zero_eq_one, one_smul]

end GlobalTheory.SplitVacF

end

namespace GlobalTheory.SplitVacF

end GlobalTheory.SplitVacF

