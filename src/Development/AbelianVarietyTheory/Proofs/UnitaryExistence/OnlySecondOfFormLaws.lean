import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ContinuousIffCrdA
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicElementLatticeFullAndCompletion
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LcscAdelicUnitaryGroup
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.InvariantProbabilityLatticeQuotientUnique
import Formalism.LocalToGlobal.GlobalTheory.GL5.FamilyMassVolumeIdentityOfClassDecomp
import Formalism.SatakeDualWeyl.Statement

noncomputable section

namespace GlobalTheory.CoreLawsCompare

open NumberField IsDedekindDomain MeasureTheory ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.Pj GlobalTheory.IndefiniteRowSideFullHecke
open scoped TensorProduct Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7}

def DatumSign {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} (Dw : Datum H) {r : ℕ} (V' : ConjugateFieldNorm.HSpace D.host.E r)
    (ε : ℤˣ) : Prop :=
  ∃ φ : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E), Function.Injective φ ∧
    LinearMap.range φ = ConjugateFieldNorm.latAt D.host.F D.host.AA V' 1 ∧
    ∀ x y, ((Dw.EF x y : ℤ) : ℚ) =
      ((ε : ℤ) : ℚ) * Algebra.trace ℚ D.host.E (-D.host.xi0 * herm V'.Gm (φ x) (φ y))

theorem invProb_iff (V : HSp D) (hP : VolPairEx V) (hV : FinVol V) (ν : Measure (AutQ V)) :
    IsProbabilityMeasure ν ∧ RightInv V ν ↔ ν = muQ1 V := by
  have hp := volPair_isVolPair V hP
  obtain ⟨i1, i2, i3⟩ := _root_.GlobalTheory.AdelicUnitaryTop.lcsc_adelicUnitary _ _ D.sp.cm.sig _ V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.topGroupHA D.sp.cm.sig V.gram
  have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.borelHA D.sp.cm.sig V.gram
  have : Countable (GQ V) := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.countableGamma D.sp.cm.sig V.gram
  have : (volPair V).1.IsHaarMeasure := hp.1.1
  have hV' := hV
  rw [FinVol, muQ_univ] at hV'
  have hq : muQ1 V = ((volPair V).1 (volPair V).2)⁻¹ • ((volPair V).1.restrict (volPair V).2).map (autMk V) := by
    rw [muQ1, if_pos (show _ ∧ _ from hV), muQ_univ]; rfl
  constructor
  · rintro ⟨h1, h2⟩
    rw [hq]
    exact _root_.GlobalTheory.LatticeQuotUniq.invariant_prob_eq _ (GQ V) _ _ hp.2 hV'.2 ν h2
  · rintro rfl
    refine ⟨inferInstance, fun h ρ hρ s hs => ?_⟩
    have hm := autMk_measurable V
    have e : autMk V ⁻¹' (ρ ⁻¹' s) = (· * h) ⁻¹' (autMk V ⁻¹' s) := by
      ext g; exact iff_of_eq (congrArg (· ∈ s) (hρ g))
    have hs' : MeasurableSet (ρ ⁻¹' s) := by
      change MeasurableSet (autMk V ⁻¹' (ρ ⁻¹' s))
      rw [e]; exact measurable_mul_const h (hm hs)
    have hri := GlobalTheory.AutQuotCheck.rightInvariant_of_covolume (GQ V) _ hp.2 hV'.1 hV'.2
    have : (volPair V).1.IsMulRightInvariant := ⟨hri⟩
    have hF : IsFundamentalDomain (GQ V) ((Equiv.mulRight h⁻¹) ⁻¹' (volPair V).2) (volPair V).1 :=
      hp.2.preimage_of_equiv (measurePreserving_mul_right _ h⁻¹).quasiMeasurePreserving (e := id)
        Function.bijective_id (fun γ x => by simp [Subgroup.smul_def, mul_assoc])
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.measurableConstSMul_subgroup (GQ V)
    have := Formalism.L2.GlobalTheoryTheory.GenusMassVolumes.Unfold.smulInvariant_subgroup (GQ V) (volPair V).1
    rw [hq, Measure.smul_apply, Measure.smul_apply]
    congr 1
    rw [show ((volPair V).1.restrict (volPair V).2).map (autMk V) s = _ from
      congrArg (fun m : Measure (AutQ V) => m s) (GlobalTheory.AutQuotCheck.map_restrict_eq (GQ V) _ hp.2 hF),
      Measure.map_apply hm hs', Measure.map_apply hm hs, Measure.restrict_apply (hm hs'),
      Measure.restrict_apply (hm hs), e, ← measure_preimage_mul_right (volPair V).1 h (_ ∩ _ ⁻¹' _)]
    congr 1
    ext g
    simp

def SpaceW (T : Core D) : Prop := ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → T.V j σ = D.sp.W j

variable {T : Core D} (hW : SpaceW T)

variable (π : Fin 2 → 𝓞 D.host.E)

end GlobalTheory.CoreLawsCompare
