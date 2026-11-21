import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.ExistsOfMemKOne

noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.SplitWeil GlobalTheory.StepData

namespace DiscreteGroups.sglob.DzIso

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)} {g : ℕ} [Fact g.Prime]
  (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

include hi

theorem norm_symm_le (y : 𝒪[w.adicCompletion E]) : ‖i.symm (y : w.adicCompletion E)‖ ≤ 1 := by
  rw [← norm_le_iff i hi, RingEquiv.apply_symm_apply]
  exact (val_le_iff _).1 ((Valuation.mem_integer_iff _ _).1 y.2)

def toIntFun (y : 𝒪[w.adicCompletion E]) : ℤ_[g] := ⟨i.symm y, norm_symm_le i hi y⟩

theorem coe_toIntFun (y : 𝒪[w.adicCompletion E]) : ((toIntFun i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def toInt : 𝒪[w.adicCompletion E] →+* ℤ_[g] where
  toFun := toIntFun i hi
  map_one' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_one]; simp)
  map_mul' a b := PadicInt.ext (by rw [PadicInt.coe_mul, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)
  map_zero' := PadicInt.ext (by rw [coe_toIntFun, PadicInt.coe_zero]; simp)
  map_add' a b := PadicInt.ext (by rw [PadicInt.coe_add, coe_toIntFun, coe_toIntFun, coe_toIntFun]; simp)

theorem coe_toInt (y : 𝒪[w.adicCompletion E]) : ((toInt i hi y : ℤ_[g]) : ℚ_[g]) = i.symm y := rfl

def redO : 𝒪[w.adicCompletion E] →+* ZMod g := (PadicInt.toZMod (p := g)).comp (toInt i hi)

theorem redO_surjective : Function.Surjective (redO i hi) := by
  intro a
  refine ⟨(a.val : 𝒪[w.adicCompletion E]), ?_⟩
  show PadicInt.toZMod (toInt i hi (a.val : 𝒪[w.adicCompletion E])) = a
  rw [map_natCast, map_natCast, ZMod.natCast_zmod_val]

theorem ker_redO : RingHom.ker (redO i hi) = IsLocalRing.maximalIdeal 𝒪[w.adicCompletion E] := by
  ext y
  rw [← IsLocalRing.residue_eq_zero_iff, residue_eq_zero_iff_lt, RingHom.mem_ker]
  show PadicInt.toZMod (toInt i hi y) = 0 ↔ _
  rw [← RingHom.mem_ker, PadicInt.ker_toZMod, IsLocalRing.mem_maximalIdeal, PadicInt.mem_nonunits, PadicInt.norm_def,
    coe_toInt, ← valuation_lt_iff i hi, RingEquiv.apply_symm_apply]

end DiscreteGroups.sglob.DzIso
