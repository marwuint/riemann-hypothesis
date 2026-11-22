import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.DataHodge
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.IsFrameOverLine
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.FrameDefinitions.Values
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.NineStatements.Twist

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree GroundTheory.Heights₂.Heights.LowerBoundFree.Line
open scoped Matrix ComplexOrder

section Bundle

variable {Ω' : Type} [Field Ω'] {κ : Type}

def twistLat (x : κ → Ω') (i : κ) : AddSubgroup (Fin 2 → Ω') where
  carrier := {e | e 0 ∈ chartRing ℤ x i ∧ x i * e 1 ∈ chartRing ℤ x i}
  add_mem' ha hb := ⟨add_mem ha.1 hb.1, by rw [Pi.add_apply, mul_add]; exact add_mem ha.2 hb.2⟩
  zero_mem' := ⟨zero_mem _, by rw [Pi.zero_apply, mul_zero]; exact zero_mem _⟩
  neg_mem' ha := ⟨neg_mem ha.1, by rw [Pi.neg_apply, mul_neg]; exact neg_mem ha.2⟩

def twW (x : κ → Ω') (i : κ) (q : Fin 2) : Ω' := if q = 0 then 1 else (x i)⁻¹

def twistVec (x : κ → Ω') (i : κ) (q : Fin 2) : Fin 2 → Ω' := twW x i q • Pi.single q 1

theorem sum_twistVec (x : κ → Ω') (i : κ) (a : Fin 2 → Ω') :
    ∑ q, a q • twistVec x i q = fun p => a p * twW x i p := by
  funext p
  fin_cases p <;> simp [twistVec, Fin.sum_univ_two, twW]

theorem twW_ne_zero {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) : twW x i q ≠ 0 := by
  unfold twW
  split_ifs
  · exact one_ne_zero
  · exact inv_ne_zero hi

def twistBasis {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) : Module.Basis (Fin 2) Ω' (Fin 2 → Ω') :=
  (Pi.basisFun Ω' (Fin 2)).isUnitSMul (w := twW x i) fun q => (twW_ne_zero hi q).isUnit

theorem twistBasis_apply {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (q : Fin 2) :
    twistBasis hi q = twistVec x i q := by
  rw [twistBasis, Module.Basis.isUnitSMul_apply, Pi.basisFun_apply]
  rfl

theorem twistVec_linearIndependent {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    LinearIndependent Ω' (twistVec x i) := by
  have := (twistBasis hi).linearIndependent
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twistVec_span {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) :
    Submodule.span Ω' (Set.range (twistVec x i)) = ⊤ := by
  have := (twistBasis hi).span_eq
  rwa [show ⇑(twistBasis hi) = twistVec x i from funext (twistBasis_apply hi)] at this

theorem twist_frame_iff {x : κ → Ω'} {i : κ} (hi : x i ≠ 0) (e : Fin 2 → Ω') :
    (∃ n : ℕ, (1 : Ω') ^ n • e ∈ twistLat x i) ↔
      ∃ a : Fin 2 → Ω', (∀ q, ∃ n : ℕ, (1 : Ω') ^ n * a q ∈ chartRing ℤ x i) ∧
        e = ∑ q, a q • twistVec x i q := by
  simp only [one_pow, one_smul, one_mul, exists_const, sum_twistVec]
  constructor
  · rintro ⟨h0, h1⟩
    refine ⟨fun q => if q = 0 then e 0 else x i * e 1, fun q => ?_, ?_⟩
    · fin_cases q
      · simpa using h0
      · simpa using h1
    · funext p
      fin_cases p
      · simp [twW]
      · simp [twW]
        field_simp
  · rintro ⟨a, ha, rfl⟩
    refine ⟨by simpa [twW] using ha 0, ?_⟩
    have h1 : x i * (a 1 * twW x i 1) = a 1 := by
      simp only [twW, if_neg (show (1 : Fin 2) ≠ 0 by decide)]
      field_simp
    rw [h1]
    simpa using ha 1

def twistBundle (x : κ → Ω') : ChartBundle ℤ x 2 (Fin 2 → Ω') where
  lat := twistLat x
  stable i a ha e he := ⟨by simpa [smul_eq_mul] using mul_mem ha he.1,
    by simpa [smul_eq_mul, mul_left_comm] using mul_mem ha he.2⟩
  frame i hi := ⟨1, fun _ => 1, fun _ => 1, fun _ => one_mem _, fun _ => one_mem _, by simp,
    fun _ => ⟨twistVec x i, twistVec_linearIndependent hi, twistVec_span hi, twist_frame_iff hi⟩⟩
  overlap i j hi hj e he := by
    obtain ⟨m0, hm0⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.1
    obtain ⟨m1, hm1⟩ := exists_pow_mul_mem_chartRing (o := ℤ) x i j hi he.2
    have hij : x i / x j ∈ chartRing ℤ x j := div_mem_chartRing x j i
    set r := x i / x j with hr
    refine ⟨m0 + m1 + 1, ?_, ?_⟩
    · have : (r ^ (m0 + m1 + 1) • e) 0 = r ^ (m1 + 1) * (r ^ m0 * e 0) := by
        rw [Pi.smul_apply, smul_eq_mul]; ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm0
    · have hxx : x j * r = x i := mul_div_cancel₀ _ hj
      have : x j * (r ^ (m0 + m1 + 1) • e) 1 = r ^ m0 * (r ^ m1 * (x i * e 1)) := by
        rw [Pi.smul_apply, smul_eq_mul, ← hxx]
        ring
      rw [this]
      exact mul_mem (pow_mem hij _) hm1

end Bundle

abbrev ch (l : Fin 2) : Unit → Fin 2 := fun _ => l

theorem isValueAt_ratio (l l' : Fin 2) {z : (Σ _ : Unit, Fin 2) → ℂ} (hz : z ⟨(), l'⟩ ≠ 0) :
    IsValueAt yLine (yLine ⟨(), l⟩ / yLine ⟨(), l'⟩) z (z ⟨(), l⟩ / z ⟨(), l'⟩) := by
  have h := isMultiHomog_prod_X (ι := PBlk 2) (ch l)
  have h' := isMultiHomog_prod_X (ι := PBlk 2) (ch l')
  refine ⟨fun _ => 1, ∏ k, X ⟨k, ch l k⟩, ∏ k, X ⟨k, ch l' k⟩, h, h', ?_, ?_, ?_, ?_⟩
  · simpa using yLine_ne_zero ⟨(), l'⟩
  · simp only [aeval_X, Fintype.prod_unique]
    exact (div_mul_cancel₀ _ (yLine_ne_zero _)).symm
  · simpa using hz
  · simp

end GroundTheory.Heights₂.Heights.NineStatements.Twist
