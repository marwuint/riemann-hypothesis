import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ThetaEqB
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubSelf
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityUnitary
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HypothesesAbsDet
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjUInvMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IsThetaSubGAlgDOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsRealmapsIsomorphism
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsOneParamSubgroupTransposeGramLieAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EigenIntertwinerSkewPlaneUniqueDual
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineOneParameter
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionUnitaryCompact
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPairingStdP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulRealAdEqZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilLineCmModelSum
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SchwartzTendstoOperatorCurveOfPointwise
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzMapBarrelledSpace

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm GlobalTheory.SquareAgree
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

namespace GlobalTheory.ArchProdRule

open Filter Topology

theorem slope_prod {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V] :
    ∀ (k : ℕ) (T : Fin k → ℝ → SchwartzMap V ℂ →ₗ[ℂ] SchwartzMap V ℂ) (Q : Fin k → SchwartzMap V ℂ → SchwartzMap V ℂ),
    (∀ i t, Continuous (T i t)) → (∀ i f, T i 0 f = f) →
    (∀ i f, Tendsto (fun t : ℝ => t⁻¹ • (T i t f - f)) (𝓝[≠] 0) (𝓝 (Q i f))) →
    ∀ f, Tendsto (fun t : ℝ => t⁻¹ • ((List.ofFn fun i => T i t).prod f - f)) (𝓝[≠] 0) (𝓝 (∑ i, Q i f)) := by
  intro k
  induction k with
  | zero =>
    intro T Q _ _ _ f
    simpa using (tendsto_const_nhds (x := (0 : SchwartzMap V ℂ)) (f := 𝓝[≠] (0 : ℝ)))
  | succ k ih =>
    intro T Q hc h0 hQ f
    have ht := ih (fun i => T i.succ) (fun i => Q i.succ) (fun i => hc i.succ) (fun i => h0 i.succ)
      (fun i => hQ i.succ) f
    let S : ℝ → SchwartzMap V ℂ →L[ℂ] SchwartzMap V ℂ := fun t => ⟨T 0 t, hc 0 t⟩
    have hS1 : ∀ g, Tendsto (fun t => S t g) (𝓝[≠] 0) (𝓝 g) := by
      intro g
      have h2 : Tendsto (fun t : ℝ => t • (t⁻¹ • (T 0 t g - g)) + g) (𝓝[≠] 0) (𝓝 ((0 : ℝ) • Q 0 g + g)) :=
        ((tendsto_nhdsWithin_of_tendsto_nhds tendsto_id).smul (hQ 0 g)).add_const g
      rw [zero_smul, zero_add] at h2
      refine h2.congr' (eventually_nhdsWithin_of_forall fun t ht => ?_)
      rw [smul_smul, mul_inv_cancel₀ ht, one_smul, sub_add_cancel]
      rfl
    have h1 := _root_.GlobalTheory.schwartz_tendsto_apply_of_tendsto_pointwise V S hS1 _ _ ht
    have h3 := h1.add (hQ 0 f)
    rw [Fin.sum_univ_succ, add_comm (Q 0 f)]
    refine h3.congr fun t => ?_
    have e : (List.ofFn fun i => T i t).prod f = T 0 t ((List.ofFn fun i : Fin k => T i.succ t).prod f) := by
      rw [List.ofFn_succ, List.prod_cons]
      rfl
    rw [e]
    show T 0 t (t⁻¹ • ((List.ofFn fun i : Fin k => T i.succ t).prod f - f)) + _ = _
    rw [LinearMap.map_smul_of_tower, map_sub, ← smul_add, sub_add_sub_cancel]

end GlobalTheory.ArchProdRule
