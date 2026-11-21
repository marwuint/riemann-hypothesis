import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.UpperOff
import Formalism.HermitianCurvature.HermitianCurvatureProofs.HeisenbergLeviConjugationMeasure

noncomputable section

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.Amp.Model

def sw : Mat 2 1 := (!![0,0,0,0,1; 0,1,0,0,0; 0,0,1,0,0; 0,0,0,1,0; 1,0,0,0,0] : Matrix (Fin 5) (Fin 5) ℂ)

def z1 : Fin (2 * 1 + 2 + 1) → ℂ := (![0,0,1,2,0] : Fin 5 → ℂ)

def xx : Mat 2 1 := (!![1,-1,0,0,-1/2; 0,1,0,0,1; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)

def xi : Mat 2 1 := (!![1,1,0,0,-1/2; 0,1,0,0,-1; 0,0,1,0,0; 0,0,0,1,0; 0,0,0,0,1] : Matrix (Fin 5) (Fin 5) ℂ)

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.det_upper {r : ℕ} (x : _root_.GlobalTheory.Amp.UT r → ℂ) :
    (_root_.GlobalTheory.Amp.upper x).det = 1 := by
  rw [Matrix.det_of_upperTriangular]
  · exact Finset.prod_eq_one fun i _ => by simp [_root_.GlobalTheory.Amp.upper]
  · intro i j hij
    simp only [id] at hij
    have h1 : ¬ i < j := not_lt.mpr hij.le
    simp [_root_.GlobalTheory.Amp.upper, h1, hij.ne']

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_uEmb (k r : ℕ) :
    Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper x) := by
  have hup : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      _root_.GlobalTheory.Amp.upper x := by
    refine continuous_pi fun a => continuous_pi fun b => ?_
    unfold _root_.GlobalTheory.Amp.upper
    split_ifs
    · exact continuous_apply _
    · exact continuous_const
    · exact continuous_const
  have hinv : ∀ x : _root_.GlobalTheory.Amp.UT r → ℂ,
      (_root_.GlobalTheory.Amp.upper x)⁻¹ = (_root_.GlobalTheory.Amp.upper x).adjugate := by
    intro x; rw [Matrix.inv_def, _root_.GlobalTheory.Amp.Model.det_upper]; simp
  have hc : Continuous fun x : _root_.GlobalTheory.Amp.UT r → ℂ =>
      (_root_.GlobalTheory.Amp.upper x)⁻¹ := by
    simp_rw [hinv]; exact hup.matrix_adjugate
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.uEmb
  split_ifs
  · exact (continuous_apply_apply _ _).comp hup
  · exact ((continuous_apply_apply _ _).comp hc).star
  · exact continuous_const
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_pOf (k r : ℕ) :
    Continuous (_root_.GlobalTheory.Amp.pOf k r) := by
  have herm : ∀ {f g : _root_.GlobalTheory.Amp.PPar k r → Fin (k + 1) → ℂ},
      Continuous f → Continuous g → Continuous fun q => _root_.Formalism.QuantumDeterminants.herm (_root_.Formalism.QuantumDeterminants.Hb k) (f q) (g q) :=
    fun hf hg => (_root_.Formalism.FourierDecayAlt.P.B2x5.continuous_herm (_root_.Formalism.QuantumDeterminants.Hb k)).comp (hf.prodMk hg)
  have hB : ∀ a, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r => q.1 a :=
    fun a => (continuous_apply a).comp continuous_fst
  have hS : ∀ a b, Continuous fun q : _root_.GlobalTheory.Amp.PPar k r =>
      _root_.GlobalTheory.Amp.skewM q.2.1 q.2.2 a b := by
    intro a b
    unfold _root_.GlobalTheory.Amp.skewM
    split_ifs
    · exact (continuous_apply _).comp (continuous_fst.comp continuous_snd)
    · exact ((continuous_apply _).comp (continuous_fst.comp continuous_snd)).star.neg
    · exact (Complex.continuous_ofReal.comp
        ((continuous_apply _).comp (continuous_snd.comp continuous_snd))).mul continuous_const
  refine continuous_pi fun i => continuous_pi fun j => ?_
  unfold _root_.GlobalTheory.Amp.pOf _root_.GlobalTheory.Amp.pEl
  split_ifs
  · exact continuous_const
  · exact (herm continuous_const (hB _)).neg
  · exact (continuous_apply _).comp (hB _)
  · exact (hS _ _).sub ((herm (hB _) (hB _)).div_const _)
  · exact continuous_const

open MeasureTheory Matrix in
open scoped InnerProductSpace ENNReal in
theorem _root_.GlobalTheory.Amp.Model.cont_lebN_map (k r : ℕ) :
    Continuous fun q : (_root_.GlobalTheory.Amp.UT r → ℂ) × _root_.GlobalTheory.Amp.PPar k r =>
      (Matrix.of.symm (_root_.GlobalTheory.Amp.uEmb k r (_root_.GlobalTheory.Amp.upper q.1) *
        _root_.GlobalTheory.Amp.pOf k r q.2) : _root_.Formalism.QuantumDeterminants.Mt k r) := by
  exact ((_root_.GlobalTheory.Amp.Model.cont_uEmb k r).comp continuous_fst).matrix_mul
    ((_root_.GlobalTheory.Amp.Model.cont_pOf k r).comp continuous_snd)

end GlobalTheory.Amp.Model
