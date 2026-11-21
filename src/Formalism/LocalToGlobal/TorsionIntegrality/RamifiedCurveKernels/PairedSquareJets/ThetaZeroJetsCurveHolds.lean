import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.StatementT
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.Hurwitz
import Formalism.LocalToGlobal.TorsionIntegrality.RamifiedCurveKernels.PairedSquareJets.HurwitzB
import Formalism.LocalToGlobal.TorsionIntegrality.SecondCoefficientNorms.CurveSecondLogDerivative
import Formalism.LocalToGlobal.TorsionIntegrality.WeierstrassTwoTorsion.BridgeTwoMore
import Formalism.GaussJetBounds.FinalB

noncomputable section
open scoped BigOperators
open Finset

namespace Formalism.L2.Th1.G

open Formalism.L2.Th1.C
open Formalism.L2.Th1.A (logSer expSer wpReg xPlus)
open Formalism.G (unitBall)
open Formalism.DworkPowerSeriesWeights (JetsIntegral jetPair)

namespace GramFrameCompositionTwoFacts

section Hom

variable {K : Type} [Field K]

theorem mvSubst_subst {σ τ : Type} {a : σ → MvPowerSeries τ K} (ha : MvPowerSeries.HasSubst a)
    {g : MvPowerSeries σ K} (hg : MvPowerSeries.constantCoeff g = 0) (f : PowerSeries K) :
    MvPowerSeries.subst a (PowerSeries.subst g f) = PowerSeries.subst (MvPowerSeries.subst a g) f := by
  rw [PowerSeries.subst_def, PowerSeries.subst_def,
    MvPowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero hg).const ha]

theorem cc_zPt {n : Type} {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) (i : n) :
    MvPowerSeries.constantCoeff
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K) = 0 :=
  PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) linv h0

theorem hasSubst_zPt {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries.HasSubst (fun i : n =>
      (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) linv : MvPowerSeries n K)) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero fun i => cc_zPt h0 i

def toZHom {n : Type} [Finite n] {linv : PowerSeries K} (h0 : PowerSeries.constantCoeff linv = 0) :
    MvPowerSeries n K →ₐ[K] MvPowerSeries n K :=
  MvPowerSeries.substAlgHom (hasSubst_zPt h0)

theorem toZHom_apply {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : MvPowerSeries n K) :
    toZHom h0 f = toZ linv f :=
  MvPowerSeries.substAlgHom_apply _ f

theorem toZ_subst_X {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (f : PowerSeries K) (i : n) :
    toZ linv (PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) f) =
      PowerSeries.subst (MvPowerSeries.X i : MvPowerSeries n K) (PowerSeries.subst linv f) := by
  unfold toZ
  rw [mvSubst_subst (hasSubst_zPt h0) (MvPowerSeries.constantCoeff_X i),
    MvPowerSeries.subst_X (hasSubst_zPt h0),
    PowerSeries.subst_comp_subst_apply (PowerSeries.HasSubst.of_constantCoeff_zero' h0)
      (PowerSeries.HasSubst.of_constantCoeff_zero (MvPowerSeries.constantCoeff_X i))]

theorem toZ_phSum {n : Type} [Fintype n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) (c : n → K) (ph : PowerSeries K) :
    toZ linv (phSum c ph) = phSum c (PowerSeries.subst linv ph) := by
  unfold phSum
  rw [← toZHom_apply h0, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, toZHom_apply, toZ_subst_X h0]

theorem cc_phSum {n : Type} [Fintype n] (c : n → K) {ph : PowerSeries K}
    (h0 : PowerSeries.constantCoeff ph = 0) : MvPowerSeries.constantCoeff (phSum c ph) = 0 := by
  unfold phSum
  rw [map_sum]
  refine Finset.sum_eq_zero fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul, map_mul,
    PowerSeries.constantCoeff_subst_eq_zero (MvPowerSeries.constantCoeff_X i) ph h0, mul_zero]

theorem jetsIn_phSum [CharZero K] {R : Subring K} {n : Type} [Fintype n]
    {c : n → K} (hc : ∀ i, c i ∈ R) {f : PowerSeries K} (hf : JetsIn1 R f) :
    JetsIn R (phSum c f) := by
  unfold phSum
  refine jetsIn_sum _ _ fun i _ => ?_
  rw [MvPowerSeries.smul_eq_C_mul]
  exact jetsIn_mul (jetsIn_C (hc i))
    (jetsIn_subst_one hf (MvPowerSeries.constantCoeff_X i) (jetsIn_X i))

theorem jetsIn_toZ [CharZero K] {R : Subring K} {l linv : PowerSeries K}
    (h : IsLogPair l linv) (hl : IsOneUnit R (PowerSeries.derivative K l)) {n : Type} [Fintype n]
    {G : MvPowerSeries n K} (hG : IntMv R G) : JetsIn R (toZ linv G) :=
  IntMvZ_of (JetsSubst_of jets_ring_holds jets_div_pow_holds) integral_jets_holds jets_subst_one_holds
    jets_ring_holds K R l linv h hl n G hG

theorem toZ_mvExp [CharZero K] {n : Type} [Finite n] {linv : PowerSeries K}
    (h0 : PowerSeries.constantCoeff linv = 0) {f : MvPowerSeries n K}
    (hf : MvPowerSeries.constantCoeff f = 0) : toZ linv (mvExp f) = mvExp (toZ linv f) :=
  mvSubst_mvExp hf (hasSubst_zPt h0)

end Hom

end GramFrameCompositionTwoFacts

open GramFrameCompositionTwoFacts

theorem kernel_two_holds : KernelTwo := by
  intro K _ _ _ l linv ph h hl hph hj n _ c hc G hG
  have hv : PowerSeries.constantCoeff linv = 0 := h.2.2.1
  have j0 : JetsIn1 (unitBall K) (PowerSeries.subst linv ph) := by
    refine (jets_of_dist_jets_holds K (unitBall K) l linv ph h).1 fun i => ?_
    rcases Nat.eq_zero_or_pos i with hi | hi
    · subst hi
      have : jet l ph 0 = 0 := hph
      rw [this]
      exact (unitBall K).zero_mem
    · exact hj i hi
  have cz : PowerSeries.constantCoeff (PowerSeries.subst linv ph) = 0 := by
    rw [JetSubstitutionLemmas.cc_subst1 hv, hph]
  have c1 : MvPowerSeries.constantCoeff (-(phSum c ph)) = 0 := by
    rw [map_neg, cc_phSum c hph, neg_zero]
  have c3 : MvPowerSeries.constantCoeff (-(phSum c (PowerSeries.subst linv ph))) = 0 := by
    rw [map_neg, cc_phSum c cz, neg_zero]
  have e : toZ linv (-(phSum c ph)) = -(phSum c (PowerSeries.subst linv ph)) := by
    rw [← toZHom_apply hv, map_neg, toZHom_apply, toZ_phSum hv]
  have key : JetsIntegral (toZ linv (mvExp (-(phSum c ph)) * G)) := by
    rw [← toZHom_apply hv, map_mul, toZHom_apply, toZHom_apply, toZ_mvExp hv c1, e]
    exact jetsIn_mul (R := unitBall K) (jetsIn_mvExp c3 (jetsIn_neg (jetsIn_phSum hc j0)))
      (jetsIn_toZ h hl hG)
  exact ⟨key, fun P hP => Formalism.DworkPowerSeriesWeights.intOp K n _ key P hP⟩

end Formalism.L2.Th1.G
