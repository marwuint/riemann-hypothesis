import Mathlib
import GroundTheory.GlobalFields.Artin.ConductorInflation
import GroundTheory.GlobalFields.Artin.OneDim
import GroundTheory.LocalFields.ArtinConductorMax
import GroundTheory.LocalFields.SeparableClosure

noncomputable section

open IsDedekindDomain NumberField GroundTheory.LocalField Module

open scoped GroundTheory.Global.SemiLocal Pointwise

namespace GroundTheory.Global

open IdeleGroup

section Units

open ValuativeRel

variable {K : Type*} [Field K] [NumberField K]

theorem unitFiltrationUnits_eq_unitsLevel (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    unitFiltrationUnits (v.adicCompletion K) n = unitsLevel v n := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact unitFiltrationUnits_zero_eq_unitsLevel_zero v
  ext x
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[v.adicCompletion K]
  rw [mem_unitFiltrationUnits_iff hn hϖ, mem_unitsLevel_of_one_le hn, ← map_pow,
    (isEquiv_valuation_valued v).le_iff_le, map_pow, valued_irreducible_valuationInteger v hϖ,
    ← WithZero.exp_nsmul]
  simp

end Units

end GroundTheory.Global
