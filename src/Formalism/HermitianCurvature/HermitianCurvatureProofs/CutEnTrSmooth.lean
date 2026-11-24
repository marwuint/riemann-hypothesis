module

public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnCut
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellHermitian
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.BigCellOpenDomain
public import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutEnFibMem
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Data.Nat.Choose.Multinomial
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
import Mathlib.Tactic.Linter.HaveILetI
import Mathlib.Tactic.Linter.Style
import Mathlib.Tactic.NormNum.Irrational
import Mathlib.Tactic.NormNum.IsCoprime
import Mathlib.Tactic.NormNum.IsSquare
import Mathlib.Tactic.NormNum.LegendreSymbol
import Mathlib.Tactic.NormNum.ModEq
import Mathlib.Tactic.NormNum.NatFib
import Mathlib.Tactic.NormNum.NatLog
import Mathlib.Tactic.NormNum.NatSqrt
import Mathlib.Tactic.NormNum.Ordinal
import Mathlib.Tactic.NormNum.Parity
import Mathlib.Tactic.NormNum.Prime
import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Topology.Sheaves.Init

@[expose] public section

open Formalism.FourierDecayAlt MeasureTheory
open Formalism.REAL Formalism.QuantumDeterminants
open NumberField
open scoped ContDiff

namespace Formalism.FourierDecayAlt.P.CutMP.En

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem hsVec_contDiff {V W : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W] :
    ContDiff ℝ ∞ (fun A : W →L[ℂ] V => B.hsVec A) := by
  let L : (W →L[ℂ] V) →ₗ[ℝ] PiLp 2 (fun _ : Fin (Module.finrank ℂ W) => V) :=
    { toFun := fun A => B.hsVec A
      map_add' := fun A A' => by ext i; simp [B.hsVec]
      map_smul' := fun c A => by ext i; simp [B.hsVec] }
  haveI : FiniteDimensional ℝ (W →L[ℂ] V) := FiniteDimensional.complexToReal _
  exact (LinearMap.toContinuousLinearMap L).contDiff

theorem wq_contDiff (k r : ℕ) (TT : ℝ) : ContDiff ℝ ∞ (fun x : MA.E r => MA.wq k x TT) := by
  have hn : ContDiff ℝ ∞ (fun z : ℂ => Complex.normSq z) := by
    simp_rw [Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  unfold MA.wq
  apply ContDiff.mul
  · apply contDiff_prod
    exact fun l _ => (hn.comp ((contDiff_apply ℝ (fun _ => ℂ) l).comp contDiff_fst)).pow _
  · exact ((hn.comp contDiff_snd).sub contDiff_const).pow _

theorem wq_pos {k r : ℕ} {TT : ℝ} {x : MA.E r} (hx : x ∈ MA.Qset r TT) : 0 < MA.wq k x TT := by
  obtain ⟨h1, h2⟩ := hx
  unfold MA.wq
  apply mul_pos
  · exact Finset.prod_pos (fun l _ => pow_pos (Complex.normSq_pos.mpr (h1 l)) _)
  · exact pow_pos (by linarith) _

theorem trace_smoothness : TrSmooth := by
  intro E _ _ _ Wp Wq _ _ _ _ _ _ S T v hIP e he J hJ ρ
  obtain ⟨-, -, -, hTz, hTz', -, -⟩ := hIP
  have hsub : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      q ∈ JF.QDom S.G.k S.G.r (T v).base.z (T v).base.z' := by
    intro q hq
    refine ⟨hq.1, ?_⟩
    have h2 : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have h3 : (D.parOf S v).TT = (D.parOf S v).T * (D.parOf S v).T' := rfl
    rwa [h3, ← hTz, ← hTz'] at h2
  have hgq : ∀ q ∈ MA.Qset (D.parOf S v).r (D.parOf S v).TT,
      B.gq (T v).base q ∈ Q.Glev S.G.k S.G.r 0 ∩ OmP S T v := fun q hq =>
    om_sub' (Formalism.FourierDecayAlt.P.BigCellHermitian.gqDom (T v).base (hsub q hq))
  have hgqS : ContDiffOn ℝ ∞ (fun q => B.gq (T v).base q) (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (contDiffOn_infty.mpr fun n => Formalism.FourierDecayAlt.P.BigCellOpenDomain.gq_contDiffOn (T v).base n).mono hsub
  have hJq : ContDiffOn ℝ ∞ (fun q => B.hsVec (J (B.gq (T v).base q)))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) := by
    intro x hx
    obtain ⟨U, F, hU, hxU, hF, hJF⟩ := hJ.1 _ (hgq x hx)
    have hFat : ContDiffAt ℝ ∞ F (B.gq (T v).base x) := hF.contDiffAt (hU.mem_nhds hxU)
    have h1 : ContDiffWithinAt ℝ ∞ (fun q => F (B.gq (T v).base q))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x := hFat.comp_contDiffWithinAt x (hgqS x hx)
    have h2 : ContDiffWithinAt ℝ ∞ (fun q => B.hsVec (F (B.gq (T v).base q)))
        (MA.Qset (D.parOf S v).r (D.parOf S v).TT) x :=
      (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).contDiffAt.comp_contDiffWithinAt x h1
    refine h2.congr_of_eventuallyEq ?_ ?_
    · have hpre := (hgqS x hx).continuousWithinAt.preimage_mem_nhdsWithin (hU.mem_nhds hxU)
      filter_upwards [hpre, self_mem_nhdsWithin] with y hyU hyQ
      rw [hJF _ hyU (hgq y hyQ).1]
    · rw [hJF _ hxU (hgq x hx).1]
  have he2 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => B.hsVec (e ρ q.2))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (hsVec_contDiff (V := Wp (S.pl v)) (W := Wq (S.pl v))).comp_contDiffOn
      ((he.1 ρ).comp contDiff_snd.contDiffOn (fun q hq => hq.2))
  have hw0 : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r => Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    (wq_contDiff _ _ _).contDiffOn.sqrt fun q hq => (wq_pos hq).ne'
  have hw : ContDiffOn ℝ ∞ (fun q : MA.E (D.parOf S v).r =>
      ((Real.sqrt (MA.wq S.G.k q (D.parOf S v).TT) : ℝ) : ℂ))
      (MA.Qset (D.parOf S v).r (D.parOf S v).TT) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn hw0
  have hF := hw.mul (ContDiffOn.inner ℂ he2 hJq)
  show ContDiffOn ℝ MA.sm (MA.ext _) (MA.Qset (D.parOf S v).r (D.parOf S v).TT)
  refine hF.congr ?_
  intro x hx
  rw [MA.ext, dite_eq_left hx]

end Formalism.FourierDecayAlt.P.CutMP.En
