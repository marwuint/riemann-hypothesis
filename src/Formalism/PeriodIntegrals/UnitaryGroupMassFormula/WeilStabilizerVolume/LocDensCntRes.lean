import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TopoAF
import Formalism.PeriodIntegrals.VolFromSW
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.T2SpaceTensorProductFiniteExtension
import ReciprocityTheory.GeneralLinearIntegers.AlgebraMapIntMemOint
import Formalism.PeriodIntegrals.WeilQuotMeas
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.StepBruhat
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.LintegralMulAvgComm
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilQuotientMeasure.Bruhat
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.QuotMeasUniq
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.DensGen
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.TensTop
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.ExistsUnifFv

noncomputable section

namespace PI.VolStabW

open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

section Res

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

abbrev iO (a : 𝓞 F) : Fv F v := algebraMap F (Fv F v) (algebraMap (𝓞 F) F a)

theorem vcoe (x : F) : Valued.v (algebraMap F (Fv F v) x) = v.valuation F x := by
  rw [HeightOneSpectrum.algebraMap_adicCompletion, Function.comp_apply, Algebra.algebraMap_self,
    RingHom.id_apply, v.valuedAdicCompletion_eq_valuation']

theorem v_iO_le (a : 𝓞 F) : Valued.v (iO v a) ≤ 1 := by
  rw [vcoe]; exact v.valuation_le_one a

theorem v_iO_lt_iff (a : 𝓞 F) : Valued.v (iO v a) < 1 ↔ a ∈ v.asIdeal := by
  rw [vcoe]; exact v.valuation_lt_one_iff_mem a

theorem exists_appr {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 := by
  have hU : IsOpen {y : Fv F v | Valued.v (x - y) < 1} := by
    have e : {y : Fv F v | Valued.v (x - y) < 1} = {y : Fv F v | ‖x - y‖ < 1} := by
      ext y; simp only [Set.mem_setOf_eq]; exact Valued.toNormedField.norm_lt_one_iff.symm
    rw [e]
    exact isOpen_lt (continuous_const.sub continuous_id).norm continuous_const
  obtain ⟨y, hy⟩ := (v.denseRange_algebraMap (K := F)).exists_mem_open hU
    ⟨x, by simp⟩
  simp only [Set.mem_setOf_eq] at hy
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  have hy1 : v.valuation F y ≤ 1 := by
    rw [← vcoe]
    have : algebraMap F (Fv F v) y = x - (x - algebraMap F (Fv F v) y) := by ring
    rw [this]
    exact (Valuation.map_sub _ _ _).trans (max_le hx1 hy.le)
  obtain ⟨a, ha⟩ := v.exists_valuation_sub_lt_of_integer hy1 (1 : (WithZero (Multiplicative ℤ))ˣ)
  refine ⟨a, ?_⟩
  have ha' : Valued.v (iO v a - algebraMap F (Fv F v) y) < 1 := by
    rw [iO, ← map_sub, vcoe]; simpa using ha
  have : x - iO v a = (x - algebraMap F (Fv F v) y) - (iO v a - algebraMap F (Fv F v) y) := by ring
  rw [this]
  exact Valuation.map_sub_lt _ hy ha'

open Classical in

def appr (x : Fv F v) : 𝓞 F :=
  if h : ∃ a : 𝓞 F, Valued.v (x - iO v a) < 1 then h.choose else 0

theorem appr_spec {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    Valued.v (x - iO v (appr v x)) < 1 := by
  have h := exists_appr v hx
  rw [appr, dif_pos h]
  exact h.choose_spec

def red (x : Fv F v) : 𝓞 F ⧸ v.asIdeal := Ideal.Quotient.mk _ (appr v x)

theorem red_eq_mk_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) (a : 𝓞 F) :
    red v x = Ideal.Quotient.mk _ a ↔ Valued.v (x - iO v a) < 1 := by
  rw [red, Ideal.Quotient.eq, ← v_iO_lt_iff, iO, iO, map_sub, map_sub]
  have h0 := appr_spec v hx
  constructor
  · intro h
    have : x - iO v a = (x - iO v (appr v x)) + (iO v (appr v x) - iO v a) := by ring
    rw [this]; exact Valuation.map_add_lt _ h0 h
  · intro h
    have : iO v (appr v x) - iO v a = (x - iO v a) - (x - iO v (appr v x)) := by ring
    show Valued.v (iO v (appr v x) - iO v a) < 1
    rw [this]; exact Valuation.map_sub_lt _ h h0

theorem mem_O_iO (a : 𝓞 F) : iO v a ∈ v.adicCompletionIntegers F :=
  (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).2 (v_iO_le v a)

theorem red_iO (a : 𝓞 F) : red v (iO v a) = Ideal.Quotient.mk _ a := by
  rw [red_eq_mk_iff v (mem_O_iO v a) a]
  simp

theorem red_add {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x + y) = red v x + red v y := by
  have e : red v x + red v y = Ideal.Quotient.mk _ (appr v x + appr v y) := by
    rw [map_add]; rfl
  rw [e, red_eq_mk_iff v (add_mem hx hy)]
  have : x + y - iO v (appr v x + appr v y) = (x - iO v (appr v x)) + (y - iO v (appr v y)) := by
    simp only [iO, map_add]; ring
  rw [this]
  exact Valuation.map_add_lt _ (appr_spec v hx) (appr_spec v hy)

theorem red_mul {x y : Fv F v} (hx : x ∈ v.adicCompletionIntegers F)
    (hy : y ∈ v.adicCompletionIntegers F) : red v (x * y) = red v x * red v y := by
  have e : red v x * red v y = Ideal.Quotient.mk _ (appr v x * appr v y) := by
    rw [map_mul]; rfl
  rw [e, red_eq_mk_iff v (mul_mem hx hy)]
  have : x * y - iO v (appr v x * appr v y) =
      x * (y - iO v (appr v y)) + iO v (appr v y) * (x - iO v (appr v x)) := by
    simp only [iO, map_mul]; ring
  rw [this]
  have hx1 : Valued.v x ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers (𝓞 F) (K := F) (v := v)).1 hx
  refine Valuation.map_add_lt _ ?_ ?_
  · rw [map_mul]
    calc Valued.v x * Valued.v (y - iO v (appr v y)) ≤ 1 * Valued.v (y - iO v (appr v y)) :=
          mul_le_mul_left hx1 _
      _ < 1 := by rw [one_mul]; exact appr_spec v hy
  · rw [map_mul]
    calc Valued.v (iO v (appr v y)) * Valued.v (x - iO v (appr v x)) ≤
          1 * Valued.v (x - iO v (appr v x)) := mul_le_mul_left (v_iO_le v _) _
      _ < 1 := by rw [one_mul]; exact appr_spec v hx

theorem red_one : red v 1 = 1 := by
  have := red_iO v 1
  simpa [iO] using this

theorem red_eq_zero_iff {x : Fv F v} (hx : x ∈ v.adicCompletionIntegers F) :
    red v x = 0 ↔ Valued.v x < 1 := by
  have := red_eq_mk_iff v hx 0
  simpa [iO] using this

theorem red_zero : red v 0 = 0 := (red_eq_zero_iff v (zero_mem _)).2 (by simp)

end Res

end PI.VolStabW
