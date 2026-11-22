import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.MatchingOfParts
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatAtVAtStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfComponentTensorAdelicFunctionEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicRapidDecayOfMemAdelicSchwartzSpace
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExtendByZeroMemSchA
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.RapidDecayAdelicIntegrablePeriodisationContinuou
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TotallyRealSelfAnnihilatorAdeleCharacter
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfFourierEqZero
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

noncomputable section
namespace GlobalTheory.SplitSvN
open MeasureTheory Matrix ComplexConjugate

variable {F : Type} [Field F] [NumberField F]

theorem schA_facts (hF : IsTotallyReal F) {κ : Type} [Fintype κ] [MeasurableSpace (κ → AF F)] [BorelSpace (κ → AF F)]
    {Φ : (κ → AF F) → ℂ} (hΦ : Φ ∈ schA F κ) : Continuous Φ ∧ (∃ C, ∀ x, ‖Φ x‖ ≤ C) ∧
      ∀ μ : Measure (κ → AF F), μ.IsAddHaarMeasure → Integrable Φ μ := by
  haveI := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  let j : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let r : (κ → AF F) ≃ₜ+ (Fin (Fintype.card κ) → AF F) :=
    { toFun := fun x => x ∘ j
      invFun := fun y => y ∘ j.symm
      left_inv := fun x => funext fun i => by simp
      right_inv := fun y => funext fun i => by simp
      map_add' := fun _ _ => rfl
      continuous_toFun := continuous_pi fun i => continuous_apply _
      continuous_invFun := continuous_pi fun i => continuous_apply _ }
  have hd := GlobalTheory.SchwartzDecay.decay_of_mem_schA F _ _ (GlobalTheory.RestrSchA.mem_schA_comp_extend F j j.injective Φ hΦ)
  set Φ' := fun y : Fin (Fintype.card κ) → AF F => Φ (Function.extend j y 0) with hΦ'
  have e : Φ = Φ' ∘ r := funext fun x => by
    show Φ x = Φ (Function.extend j (x ∘ j) 0)
    congr 1
    funext i
    obtain ⟨k, rfl⟩ := j.surjective i
    rw [j.injective.extend_apply]
    rfl
  refine ⟨e ▸ hd.1.comp r.continuous, ?_, fun μ hμ => ?_⟩
  · obtain ⟨C, hC⟩ := hd.2.2 0
    exact ⟨C, fun x => by rw [e]; simpa using hC (r x)⟩
  · have hi := (GlobalTheory.decay_integrable_periodise F _ hF Φ' hd).1 (μ.map r) (r.isAddHaarMeasure_map μ)
    rw [e]
    exact hi.comp_measurable r.continuous.measurable

end GlobalTheory.SplitSvN

end
