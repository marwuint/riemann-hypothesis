import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.OnePlaceKF
import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellDecomposition
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SettingConstruction

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.CellAmp.Model

open Formalism.BasicNotions Formalism.QuantumDeterminants Formalism.MainNotions.S

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
private theorem inv_mul_conj_mul_cancel {n : Type*} [Fintype n] [DecidableEq n] (A B C D γ a : Matrix n n ℂ)
    (hγ : IsUnit γ.det) (ha : IsUnit a.det) :
    A⁻¹ * (a * B)⁻¹ * γ * (γ⁻¹ * a * γ * C) * D = A⁻¹ * B⁻¹ * γ * C * D := by
  rw [Matrix.mul_inv_rev]
  have h1 : γ * γ⁻¹ = 1 := Matrix.mul_nonsing_inv γ hγ
  have h2 : a⁻¹ * a = 1 := Matrix.nonsing_inv_mul a ha
  calc A⁻¹ * (B⁻¹ * a⁻¹) * γ * (γ⁻¹ * a * γ * C) * D
      = A⁻¹ * B⁻¹ * (a⁻¹ * ((γ * γ⁻¹) * a)) * γ * C * D := by
        simp only [Matrix.mul_assoc]
    _ = _ := by rw [h1, Matrix.one_mul, h2, Matrix.mul_one]

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.pairMaj_stabAct {k r : ℕ} (γ a : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hγ : IsUnit γ.det)
    (ha : IsUnit a.det) (b : ℝ) (p : _root_.Formalism.MainNotions.S.PairSp k r) : _root_.GlobalTheory.CellAmp.pairMaj γ b (_root_.Formalism.MainNotions.S.stabAct γ a p) = _root_.GlobalTheory.CellAmp.pairMaj γ b p :=
  congrArg (fun M => _root_.Formalism.FourierDecayAlt.B.gN M ^ (-b))
    (inv_mul_conj_mul_cancel (of p.1.1) (of p.1.2) (of p.2.2) (of p.2.1) γ a hγ ha)

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.CellAmp.Model.ell_one (k r : ℕ) (z : Fin (2 * r + k + 1) → ℂ) (hz : _root_.Formalism.QuantumDeterminants.inWb k r z) : _root_.Formalism.QuantumDeterminants.ell k r z 1 = 0 := by
  unfold _root_.Formalism.QuantumDeterminants.ell
  refine Finset.sum_eq_zero fun a _ => ?_
  split_ifs with h
  · rw [Matrix.one_apply_ne]
    intro he
    have := congrArg Fin.val he
    simp [_root_.Formalism.QuantumDeterminants.eI] at this
  · rw [Matrix.one_mulVec]
    exact hz _ (Or.inl (by simp [_root_.Formalism.QuantumDeterminants.eI]))

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in

theorem _root_.GlobalTheory.CellAmp.Model.cellData_open {k r : ℕ} (L : _root_.Formalism.MainNotions.S.LocBessel k r) (μG : Measure (_root_.Formalism.QuantumDeterminants.Mt k r))
    (g : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) (hg : g ∈ _root_.Formalism.QuantumDeterminants.UH (_root_.Formalism.QuantumDeterminants.Hpk k r)) (hinv : g⁻¹ * g = 1)
    (hG : 0 < _root_.Formalism.QuantumDeterminants.Gf k r L.z L.z' g) (hm : _root_.Formalism.FourierDecayAlt.C2.IsMonomial (_root_.Formalism.QuantumDeterminants.Zhat k r L.z L.z' g))
    (hR : _root_.Formalism.MainNotions.S.RStab k r g = {1}) :
    _root_.GlobalTheory.CellAmp.CellData L μG g (Measure.dirac (fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j)) μG (_root_.Formalism.MainNotions.S.pairMeas L) := by
  have hone : (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) = 1 := rfl
  refine ⟨hg, hG, hm, ?_, ?_, ?_, ?_⟩
  · intro a ha
    rw [hR, Set.mem_singleton_iff] at ha
    subst ha
    rw [Matrix.mul_one, hinv]
    unfold _root_.Formalism.QuantumDeterminants.psi
    rw [_root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz.1, _root_.GlobalTheory.CellAmp.Model.ell_one _ _ _ L.hz'.1]
  · refine ⟨inferInstance, Measure.dirac_ne_zero, ?_, ?_⟩
    · rw [hR, Measure.dirac_apply]
      simp only [Set.mem_singleton_iff, Set.indicator_apply, Set.mem_setOf_eq]
      rw [hone]
      simp
    · intro s hs
      rw [hR, Set.mem_singleton_iff] at hs
      subst hs
      have hid : _root_.Formalism.QuantumDeterminants.lmulM (k := k) (r := r) 1 = id := funext fun x => by
        unfold _root_.Formalism.QuantumDeterminants.lmulM
        rw [Matrix.one_mul]
        rfl
      rw [hid, Measure.map_id]
  · intro f hf
    have hstab : ∀ x, _root_.Formalism.MainNotions.S.stabAct g (of fun i j => (1 : _root_.Formalism.MainNotions.S.MatKR k r) i j) x = x := by
      intro x
      unfold _root_.Formalism.MainNotions.S.stabAct
      rw [hone, Matrix.one_mul, Matrix.mul_one, hinv, Matrix.one_mul]
      rfl
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hstab]
  · intro f hf
    rw [Measure.map_congr (ae_eq_dirac _)]
    erw [Measure.map_const]
    rw [measure_univ, one_smul]
    refine lintegral_congr fun x => ?_
    rw [lintegral_dirac, hone, Matrix.mul_one, hinv, hone, Matrix.one_mul]
    rfl

end GlobalTheory.CellAmp.Model

end
