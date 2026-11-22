import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.LocalLanglandsGL
import Development.DiscreteGroups.GlobalIrreducibility.DzApprox
import Development.DiscreteGroups.GlobalIrreducibility.ExistsUniformizerValuation

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal ValuativeRel GlobalTheory.SplitWeil

namespace DiscreteGroups.sglob.DzType

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Ring

variable {Ω : Type} [Field Ω]

def kappaToA {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) : 𝓞 F →+* A :=
  ((algebraMap F Ω).comp (algebraMap (𝓞 F) F)).codRestrict A fun x =>
    mem_of_isIntegral_int A (NumberField.RingOfIntegers.isIntegral_coe x).algebraMap

def kappaQ {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω) :
    𝓞 F →+* IsLocalRing.ResidueField A :=
  (IsLocalRing.residue A).comp (kappaToA A)

theorem kappa_ker_A {F : Type} [Field F] [NumberField F] [Algebra F Ω] (A : ValuationSubring Ω)
    (v : HeightOneSpectrum (𝓞 F)) (hv : IsPlaceOver A v) :
    RingHom.ker (kappaQ A : 𝓞 F →+* IsLocalRing.ResidueField A) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaQ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff,
    ValuationSubring.valuation_lt_one_iff, ← hv y]
  rfl

end Ring

section Compl

variable {L : Type} [Field L] [NumberField L] (v : HeightOneSpectrum (𝓞 L))

theorem kappa_val_le_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y ≤ 1 ↔ Valued.v y ≤ 1 :=
  (DiscreteGroups.sglob.DzIso.val_le_iff y).trans Valued.toNormedField.norm_le_one_iff

theorem kappa_val_lt_iff (y : v.adicCompletion L) :
    valuation (v.adicCompletion L) y < 1 ↔ Valued.v y < 1 :=
  (DiscreteGroups.sglob.DzIso.val_lt_iff y).trans Valued.toNormedField.norm_lt_one_iff

theorem kappa_v_int (y : 𝓞 L) :
    Valued.v (algebraMap L (v.adicCompletion L) (y : L)) = v.valuation L (y : L) :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' (R := 𝓞 L) v (y : L)

def kappaToO : 𝓞 L →+* 𝒪[v.adicCompletion L] :=
  ((algebraMap L (v.adicCompletion L)).comp (algebraMap (𝓞 L) L)).codRestrict 𝒪[v.adicCompletion L] fun y =>
    (Valuation.mem_integer_iff _ _).2 ((kappa_val_le_iff v _).2
      ((kappa_v_int v y).trans_le (v.valuation_le_one y)))

def kappaP : 𝓞 L →+* 𝓀[v.adicCompletion L] := (IsLocalRing.residue 𝒪[v.adicCompletion L]).comp (kappaToO v)

theorem kappa_ker_O : RingHom.ker (kappaP v) = v.asIdeal := by
  ext y
  rw [RingHom.mem_ker, kappaP, RingHom.comp_apply, ← map_zero (IsLocalRing.residue 𝒪[v.adicCompletion L]),
    residue_eq_iff_valuation_lt]
  have e1 : ((kappaToO v y : 𝒪[v.adicCompletion L]) : v.adicCompletion L) -
      ((0 : 𝒪[v.adicCompletion L]) : v.adicCompletion L) = algebraMap L (v.adicCompletion L) (y : L) := by
    rw [ZeroMemClass.coe_zero, sub_zero]
    rfl
  rw [e1, kappa_val_lt_iff v, kappa_v_int v y]
  exact HeightOneSpectrum.valuation_lt_one_iff_mem v y

theorem kappa_surj_O : Function.Surjective (kappaP v) := by
  intro z
  obtain ⟨u, rfl⟩ := IsLocalRing.residue_surjective z
  have hu : Valued.v (u : v.adicCompletion L) ≤ 1 :=
    (kappa_val_le_iff v _).1 ((Valuation.mem_integer_iff _ _).1 u.2)
  obtain ⟨x, hx⟩ := exists_int_approx_compl v (u : v.adicCompletion L) hu
  refine ⟨x, ?_⟩
  rw [kappaP, RingHom.comp_apply, residue_eq_iff_valuation_lt, Valuation.map_sub_swap]
  exact (kappa_val_lt_iff v _).2 hx

end Compl

end DiscreteGroups.sglob.DzType
