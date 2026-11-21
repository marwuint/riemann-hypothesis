import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.OneMemH0WeightZero
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import GroundTheory.GlobalFields.IdeleGroups.IdeleNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneReOpenNearOfIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsQuaternionNormOneNearReSqNeOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneOfCompleteTwoNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenProd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenPi
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuaternionNormOneTraceOpenFiniteAdeleRingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyExistsQuaternionNormOneReEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InfinitePlaceCompletionNhdsNEZeroNeBot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SquaringOpenAtOneAdicCompletionNumberField

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.QSA GlobalTheory.Published
open Matrix
open scoped Quaternion Topology TensorProduct

namespace GlobalTheory.QSA

theorem traceOpen_field (K : Type) [Field K] [TopologicalSpace K] [IsTopologicalDivisionRing K] [T2Space K]
    (h2 : (2 : K) ≠ 0) (hnb : (𝓝[≠] (0 : K)).NeBot) (hsq : SqOpen K) (a b : K) (ha : a ≠ 0) : TraceOpen K a b := by
  intro g hg W hW
  obtain ⟨g', hg'1, hg're, hW'⟩ := _root_.GlobalTheory.QSA.exists_nrm_one_re_sq_ne_one K h2 hnb a b ha g hg W hW
  have hu : IsUnit (1 - g'.re ^ 2) := IsUnit.mk0 _ (sub_ne_zero.2 (Ne.symm hg're))
  obtain ⟨O, hO, hmem, hO'⟩ := _root_.GlobalTheory.traceOpen_near_of_isUnit K a b hsq g' hg'1 hu W hW'
  exact ⟨O, hO, ⟨_, hmem⟩, hO'⟩

theorem traceOpen_inf (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) :
    TraceOpen (InfiniteAdeleRing F) (algebraMap F (InfiniteAdeleRing F) a) (algebraMap F (InfiniteAdeleRing F) b) := by
  refine _root_.GlobalTheory.QSA.traceOpen_pi (InfinitePlace F) (fun w => w.Completion) _ _ (fun w => ?_)
  have h2 : (2 : w.Completion) ≠ 0 := by
    have := (map_ne_zero (algebraMap F w.Completion)).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (_root_.GlobalTheory.QSA.infinitePlace_completion_nhdsNE_neBot F w) (_root_.GlobalTheory.sqOpen_of_two_ne_zero _ h2) _ _ ((map_ne_zero (algebraMap F w.Completion)).2 ha)

theorem traceOpen_fin (F : Type) [Field F] [NumberField F] (a b : F) (ha : a ≠ 0) (hb : b ≠ 0) :
    TraceOpen (FiniteAdeleRing (𝓞 F) F) (algebraMap F (FiniteAdeleRing (𝓞 F) F) a)
      (algebraMap F (FiniteAdeleRing (𝓞 F) F) b) := by
  refine GlobalTheory.T.quaternionNormOneTraceOpen_finiteAdeleRing F a b (fun v => ?_) (_root_.GlobalTheory.QSA.IntRep.exists_nrm_eq_one_re_eq F a b ha hb)
  have h2 : (2 : v.adicCompletion F) ≠ 0 := by
    have := (map_ne_zero (algebraMap F (v.adicCompletion F))).2 (two_ne_zero : (2 : F) ≠ 0)
    rwa [map_ofNat] at this
  exact traceOpen_field _ h2 (_root_.GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion F v).2 (_root_.GlobalTheory.QSA.sqOpen_and_nhdsNE_zero_neBot_adicCompletion F v).1 _ _ ((map_ne_zero (algebraMap F _)).2 ha)

theorem traceOpen_adele : ∀ (F : Type) [Field F] [NumberField F] (a b : F), a ≠ 0 → b ≠ 0 → ∀ g : DA F a b, nrm g = 1 → ∀ W : Set (DA F a b), W ∈ 𝓝 g → ∃ O : Set (AF F), IsOpen O ∧ O.Nonempty ∧ ∀ t ∈ O, ∃ u ∈ W, nrm u = 1 ∧ u.re = t := by
  intro F _ _ a b ha hb g hg W hW
  have H : TraceOpen (AF F) (algebraMap F (AF F) a) (algebraMap F (AF F) b) :=
    _root_.GlobalTheory.QSA.traceOpen_prod _ _ _ _ _ _ (traceOpen_inf F a b ha) (traceOpen_fin F a b ha hb)
  exact H g hg W hW
end GlobalTheory.QSA
