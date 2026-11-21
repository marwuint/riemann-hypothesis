import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesPropertiesStatement
open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

namespace GlobalTheory.SmMapAct

open PI.UpqRep

variable {k r : ℕ}

def SemiBd (R : Rep k r) (f : R.H → ℝ) : Prop :=
  ∃ (C : ℝ) (Ws : List (List (Mx k r))), 0 ≤ C ∧ (∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) ∧
    ∀ v ∈ R.sm, f v ≤ C * (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum

theorem sum_norm_nonneg (R : Rep k r) (Ws : List (List (Mx k r))) (v : R.H) :
    0 ≤ (Ws.map fun w => ‖dsigW (k := k) (r := r) R.σ w v‖).sum := by
  apply List.sum_nonneg
  intro x hx
  obtain ⟨w, _, rfl⟩ := List.mem_map.mp hx
  exact norm_nonneg _

theorem semiBd_of_cw {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp}
    (h : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B) : SemiBd R (fun v => ‖B v‖) := by
  obtain ⟨C, Ws, h1, h2⟩ := h
  exact ⟨max C 0, Ws, le_max_right _ _, h1, fun v hv => (h2 v hv).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (sum_norm_nonneg R Ws v))⟩

theorem cw_of_semiBd {Wp : Type} [NormedAddCommGroup Wp] (R : Rep k r) {B : R.H → Wp} {f : R.H → ℝ}
    (h : SemiBd R f) (hle : ∀ v ∈ R.sm, ‖B v‖ ≤ f v) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ B := by
  obtain ⟨C, Ws, _, h1, h2⟩ := h
  exact ⟨C, Ws, h1, fun v hv => (hle v hv).trans (h2 v hv)⟩

theorem SemiBd.add {R : Rep k r} {f g : R.H → ℝ} (hf : SemiBd R f) (hg : SemiBd R g) :
    SemiBd R (fun v => f v + g v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  obtain ⟨C', Ws', h0', h1', h2'⟩ := hg
  refine ⟨C + C', Ws ++ Ws', add_nonneg h0 h0', ?_, fun v hv => ?_⟩
  · intro w hw
    rcases List.mem_append.mp hw with h | h
    · exact h1 w h
    · exact h1' w h
  · have a := h2 v hv
    have b := h2' v hv
    have c := sum_norm_nonneg R Ws v
    have d := sum_norm_nonneg R Ws' v
    rw [List.map_append, List.sum_append]
    nlinarith [mul_nonneg h0 d, mul_nonneg h0' c]

theorem SemiBd.mul {R : Rep k r} {f : R.H → ℝ} (hf : SemiBd R f) {a : ℝ} (ha : 0 ≤ a) :
    SemiBd R (fun v => a * f v) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := hf
  refine ⟨a * C, Ws, mul_nonneg ha h0, h1, fun v hv => ?_⟩
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left (h2 v hv) ha

theorem semiBd_sum {R R' : Rep k r} {T : R.H → R'.H} (hT : SmMap R R' T) (Ws : List (List (Mx k r)))
    (hWs : ∀ w ∈ Ws, ∀ X ∈ w, InLieHpk k r X) :
    SemiBd R (fun v => (Ws.map fun w => ‖dsigW (k := k) (r := r) R'.σ w (T v)‖).sum) := by
  induction Ws with
  | nil => exact ⟨0, [], le_rfl, by simp, fun v _ => by simp⟩
  | cons w Ws ih =>
    have h1 := semiBd_of_cw R (hT.cont w (hWs w List.mem_cons_self))
    have h2 := ih (fun w' hw' => hWs w' (List.mem_cons_of_mem _ hw'))
    simpa only [List.map_cons, List.sum_cons] using h1.add h2

theorem cw_comp {Wp : Type} [NormedAddCommGroup Wp] {R R' : Rep k r} {T : R.H → R'.H} {Bm : R'.H → Wp}
    (hT : SmMap R R' T) (hB : PI.BesselMapUniq.IsCWCont (k := k) (r := r) R'.σ Bm) :
    PI.BesselMapUniq.IsCWCont (k := k) (r := r) R.σ (fun v => Bm (T v)) := by
  obtain ⟨C, Ws, h0, h1, h2⟩ := semiBd_of_cw R' hB
  exact cw_of_semiBd R ((semiBd_sum hT Ws h1).mul h0) (fun v hv => h2 _ (hT.mem v hv))

section DS

variable {ε : Fin (2 * r + k + 1) → Bool} {mu : Fin (2 * r + k + 1) → ℝ} {R : Rep k r}

theorem inLie_conj {g X : Mx k r} (hg : g ∈ GG k r) (hX : InLieHpk k r X) : InLieHpk k r (g⁻¹ * X * g) := by
  obtain ⟨hu, hi, -⟩ := PI.UnitaryGroupMassFormula.CapelliEig.unitary_Hecke_group k r g hg
  have hdet : IsUnit g.det := (Matrix.isUnit_iff_isUnit_det _).mp hu
  have h1 : g * g⁻¹ = 1 := Matrix.mul_nonsing_inv _ hdet
  have hg' : gᴴ * Hpk k r * g = Hpk k r := hg
  have hX' : Xᴴ * Hpk k r + Hpk k r * X = 0 := hX
  have e1 : Hpk k r * g⁻¹ = gᴴ * Hpk k r := by
    calc Hpk k r * g⁻¹ = gᴴ * Hpk k r * g * g⁻¹ := by rw [hg']
      _ = gᴴ * Hpk k r := by rw [Matrix.mul_assoc, h1, Matrix.mul_one]
  have e2 : (g⁻¹)ᴴ * Hpk k r = Hpk k r * g := by
    calc (g⁻¹)ᴴ * Hpk k r = (g⁻¹)ᴴ * (gᴴ * Hpk k r * g) := by rw [hg']
      _ = (g * g⁻¹)ᴴ * Hpk k r * g := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = Hpk k r * g := by rw [h1, Matrix.conjTranspose_one, Matrix.one_mul]
  show (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g) = 0
  calc (g⁻¹ * X * g)ᴴ * Hpk k r + Hpk k r * (g⁻¹ * X * g)
      = gᴴ * Xᴴ * ((g⁻¹)ᴴ * Hpk k r) + (Hpk k r * g⁻¹) * X * g := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    _ = gᴴ * (Xᴴ * Hpk k r + Hpk k r * X) * g := by
        rw [e1, e2]; simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [hX', Matrix.mul_zero, Matrix.zero_mul]

end DS

end GlobalTheory.SmMapAct
