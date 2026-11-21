import Mathlib
import Formalism.LocalRingCardinality.DataTheta
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AbsSubOfDisjoint
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LineMatrixKroneckerLeftFactorEqZeroOfIsPC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockActDualPairCommutingLieActions
import Development.AbelianVarietyTheory.Definitions.Foundations.HarmonicAllOfCompact

noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.JointHarm

namespace GlobalTheory.FockScalarType

variable {p q r s : ℕ}

def charSub (p q r s : ℕ) (x : ℚ) : Submodule ℂ (Pol p q r s) where
  carrier := {f | ∀ Y : Mat p q, IsKC Y → fockAct1 p q r s Y f = ((x : ℂ) * Y.trace) • f}
  add_mem' := fun ha hb Y hY => by rw [map_add, ha Y hY, hb Y hY, smul_add]
  zero_mem' := fun Y _ => by simp
  smul_mem' := fun c _ ha Y hY => by rw [map_smul, ha Y hY, smul_comm]

theorem isKC_Eab {a b : Ix p q} (hab : sameBlock a b) : IsKC (Eab a b) := by
  intro c d hcd
  rw [Eab, Matrix.single_apply, if_neg]
  rintro ⟨rfl, rfl⟩
  exact hcd hab

theorem isHW_of_mem {x : ℚ} {f : Pol p q r s} (h0 : f ≠ 0) (hf : f ∈ charSub p q r s x) :
    IsHW (fockAct1 p q r s) (fun _ => x) f := by
  refine ⟨h0, ?_, ?_⟩
  · simp only [wtSub, SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
      LinearMap.smul_apply, LinearMap.id_apply]
    intro a
    rw [hf _ (isKC_Eab (by rcases a with a | a <;> trivial))]
    simp [Eab]
  · simp only [SetLike.mem_coe, Submodule.mem_iInf, LinearMap.mem_ker]
    intro a b hab
    have h1 : sameBlock a b := by
      rcases a with a | a <;> rcases b with b | b <;> simp_all [posC, sameBlock]
    have h2 : a ≠ b := by
      rintro rfl
      rcases a with a | a <;> simp [posC] at hab
    rw [hf _ (isKC_Eab h1), Eab, Matrix.trace_single_eq_of_ne _ _ _ h2]
    simp

theorem comm_parts {Y : Mat p q} (hY : IsKC Y) {Z : Mat r s} (hZ : IsPC Z) {d : ℕ}
    {v : Pol p q r s} (hv : v ∈ homog (Ln p q r s) d) :
    fockAct1 p q r s Y (upOp (kron2 p q Z) v) = upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∧
    fockAct1 p q r s Y (dnOp (kron2 p q Z) v) = dnOp (kron2 p q Z) (fockAct1 p q r s Y v) := by
  have hK : ∀ {d : ℕ} {w : Pol p q r s}, w ∈ homog (Ln p q r s) d →
      fockAct1 p q r s Y w ∈ homog (Ln p q r s) d := fun hw =>
    GlobalTheory.FockDeg.omAct_mem_homog (GlobalTheory.FockDeg.lineMatrixKroneckerLeftFactor_eq_zero_of_isKC hY) hw
  have hc := LinearMap.congr_fun ((GlobalTheory.FockPair.pair_lie_commute p q r s).2.2 Y Z) v
  rw [Module.End.mul_apply, Module.End.mul_apply, fockAct2_eq, omAct_odd (odd_kron2 hZ),
    LinearMap.add_apply, LinearMap.add_apply, map_add] at hc
  have h1 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) ∈
      homog (Ln p q r s) (d + 2) :=
    Submodule.sub_mem _ (hK (upOp_homog _ d v hv)) (upOp_homog _ d _ (hK hv))
  have h2 : dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) ∈
      homog (Ln p q r s) (d - 2) :=
    Submodule.sub_mem _ (dnOp_homog _ d _ (hK hv)) (hK (dnOp_homog _ d v hv))
  have e : fockAct1 p q r s Y (upOp (kron2 p q Z) v) - upOp (kron2 p q Z) (fockAct1 p q r s Y v) =
      dnOp (kron2 p q Z) (fockAct1 p q r s Y v) - fockAct1 p q r s Y (dnOp (kron2 p q Z) v) := by
    linear_combination hc
  have h0 : fockAct1 p q r s Y (upOp (kron2 p q Z) v) -
      upOp (kron2 p q Z) (fockAct1 p q r s Y v) = 0 := by
    by_contra hne
    have := IsHomogeneous.inj_right h1 (e ▸ h2) hne
    omega
  exact ⟨sub_eq_zero.1 h0, (sub_eq_zero.1 (e ▸ h0)).symm⟩

theorem dnOp_mem_charSub {x : ℚ} {Z : Mat r s} (hZ : IsPC Z) {d : ℕ} {v : Pol p q r s}
    (hv : v ∈ homog (Ln p q r s) d) (hc : v ∈ charSub p q r s x) :
    dnOp (kron2 p q Z) v ∈ charSub p q r s x := fun Y hY => by
  rw [(comm_parts hY hZ hv).2, hc Y hY, map_smul]

end GlobalTheory.FockScalarType
