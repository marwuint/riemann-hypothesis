import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsWeight
import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.RealGaloisRepresentations.IwahoriSphericalTransfer.FinrankAdjoinSqrtNegOne
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSpanFormsNeBot
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.HeckeLAdicCharacterAboveIff
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.AlgebraicCharacterWD
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPolarizedTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitarisableOfIsLocCompCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitCentreDerivativeEqSumDiagonalMatrixUnits
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspidalTraceMatrixUnitsActsBySumInfinitesimalChStatement

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.Published

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

section Trace

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] {a : ℕ}

theorem zc_eq_sum_Eop : zc E a = ∑ τ : E →+* ℂ, ∑ i : Fin a, Eop τ i i := _root_.GlobalTheory.ResW.zc_eq_sum_Eop E a

theorem sum_Eop_apply {π : CuspSub E a} {τ : E →+* ℂ} {m : Multiset ℂ} (h : π.HasInfChar τ m) {φ : Sm E a}
    (hφ : φ ∈ π.V) : (∑ i : Fin a, Eop τ i i) φ = m.sum • φ := GlobalTheory.T.cuspidal_traceMatrixUnits_acts_by_sum_infinitesimalCharacter E a π τ m h φ hφ

theorem cex_eq (π : CuspSub E a) : cex (⟨a, π⟩ : Letter E) = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum := by
  refine (letter_centralExponent E ⟨a, π⟩).2.2.2.2 _ ?_
  obtain ⟨φ, hφ, h0⟩ := (Submodule.ne_bot_iff _).1 π.ne_bot
  refine ⟨φ, hφ, h0, ?_⟩
  change zc E a φ = _
  rw [zc_eq_sum_Eop, LinearMap.sum_apply, Finset.sum_smul]
  exact Finset.sum_congr rfl fun τ _ => sum_Eop_apply (ParLaws.hasInfChar_infChar (CG.mk π) τ) hφ

end Trace

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ}

theorem sum_infChar_of_isWeight {π : CuspSub E a} {wt : ℤ} (h : IsWeight π wt) :
    ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum =
      (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 := by
  set c : E →+* E := (IsCMField.complexConj E).toRingEquiv.toRingHom
  have hc : Function.Bijective fun τ : E →+* ℂ => τ.comp c := by
    refine Finite.injective_iff_bijective.1 fun τ τ' e => RingHom.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (IsCMField.complexConj E).surjective x
    exact RingHom.congr_fun e y
  have h1 : ∑ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum = ∑ τ : E →+* ℂ, ((CG.mk π).infChar τ).sum :=
    Function.Bijective.sum_comp hc (fun τ => ((CG.mk π).infChar τ).sum)
  have h2 : ∀ τ : E →+* ℂ, ((CG.mk π).infChar (τ.comp c)).sum =
      (a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ)) - ((CG.mk π).infChar τ).sum := fun τ => by
    rw [h τ, Multiset.sum_map_sub, Multiset.map_const', Multiset.sum_replicate, CG.card_infChar, Multiset.map_id',
      nsmul_eq_mul]
  have h3 := Embeddings.card E ℂ
  simp only [h2, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, h3, nsmul_eq_mul] at h1
  linear_combination -h1 / 2

end GlobalTheory.UnitLocWeight

namespace GlobalTheory.UnitLocWeight

open GlobalTheory.ResW

theorem rexp_eq {E : Type} [Field E] [NumberField E] [IsCMField E] {a : ℕ} (ha : 1 ≤ a) {π : CuspSub E a} {wt : ℤ}
    (h : IsWeight π wt) : rexp (⟨a, π⟩ : Letter E) = ((a : ℝ) - 1 - wt) / 2 := by
  have e := (cex_eq π).trans (sum_infChar_of_isWeight h)
  have hd : (0 : ℝ) < Module.finrank ℚ E := by exact_mod_cast Module.finrank_pos
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have e2 : (cex (⟨a, π⟩ : Letter E)).re = (Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 := by
    rw [e]
    have : (Module.finrank ℚ E : ℂ) * ((a : ℂ) * ((a : ℂ) - 1 - (wt : ℂ))) / 2 =
        (((Module.finrank ℚ E : ℝ) * ((a : ℝ) * ((a : ℝ) - 1 - wt)) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  unfold rexp
  change (cex (⟨a, π⟩ : Letter E)).re / ((a : ℝ) * Module.finrank ℚ E) = _
  rw [e2]
  field_simp

end GlobalTheory.UnitLocWeight
