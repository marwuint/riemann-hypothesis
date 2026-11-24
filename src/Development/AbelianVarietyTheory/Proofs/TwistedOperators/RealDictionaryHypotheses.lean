module

public import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNatMulIntegralOfIsCompact
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatFiniteAdelesMemSpanRestrictedProdu
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Combinatorics.Enumerative.DyckWord
import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
import Mathlib.Data.NNRat.Floor
import Mathlib.Geometry.Euclidean.Volume.Basic
import Mathlib.NumberTheory.Chebyshev
import Mathlib.NumberTheory.Height.NumberField
import Mathlib.NumberTheory.Height.Projectivization
import Mathlib.NumberTheory.LucasLehmer
import Mathlib.NumberTheory.SelbergSieve
import Mathlib.RingTheory.PiTensorProduct
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Echelon.Zsqrtd
import Mathlib.Tactic.Inclusion.Extension.Core.Core
import Mathlib.Tactic.Inclusion.Extension.Interval.BinarySplit
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Exp
import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Basic
import Mathlib.Tactic.Inclusion.Extension.IntervalInt.Hypotheses
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
import Mathlib.Tactic.ReduceModChar
import Mathlib.Topology.Sheaves.Init
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Definitions.Foundations.IsIwasawaOfIsCompact
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.HermitianOrthogonalExtensionData
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsVacFOfIsVacVec
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BlkGLMem

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.Doubling GlobalTheory.ChainFr GlobalTheory.IndefiniteRowSideFullHecke.MatchingAdjoints
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SquareComm
open scoped ComplexConjugate
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun

open scoped GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

noncomputable section

open scoped Classical

namespace GlobalTheory.ThetaInterchange

open Filter Topology GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n d : ℕ}
  {Y : Spc F E n} {Wd : Spc F E d}

def Good (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ))
    (Φ : (Fin n × Fin d → AF F) → ℂ) : Prop :=
  Φ ∈ schA F (Fin n × Fin d) ∧ ∃ Φ' ∈ schA F (Fin n × Fin d), (∀ x, HasDerivAt (fun t => T t Φ x) (Φ' x) 0) ∧
    ∀ w, HasDerivAt (fun t => thetaSum F (M.co.rho ψ w (T t Φ))) (thetaSum F (M.co.rho ψ w Φ')) 0

theorem rho_add (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E))
    (a b : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (a + b) = M.co.rho ψ w a + M.co.rho ψ w b := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, mul_add]

theorem rho_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : M.co.rho ψ w (c • a) = c • M.co.rho ψ w a := by
  funext x
  simp only [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr, Pi.smul_apply, smul_eq_mul]
  ring

theorem rho_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) :
    M.co.rho ψ w (0 : (Fin n × Fin d → AF F) → ℂ) = 0 := by
  funext x
  simp [GlobalTheory.WeilM.Darboux.rho, GlobalTheory.WeilM.schr]

theorem theta_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ) (w : Matrix (Fin n) (Fin d) (AE F E))
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : a ∈ schA F (Fin n × Fin d)) (hb : b ∈ schA F (Fin n × Fin d)) :
    thetaSum F (M.co.rho ψ w (a + b)) = thetaSum F (M.co.rho ψ w a) + thetaSum F (M.co.rho ψ w b) := by
  rw [rho_add]
  unfold GlobalTheory.WeilM.thetaSum
  exact (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ ha)).tsum_add
    (GlobalTheory.WeilM.summable_of_mem_schA F (GlobalTheory.HeisSchA.rho_mem_schA M ψ hψ w _ hb))

theorem theta_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (w : Matrix (Fin n) (Fin d) (AE F E)) (c : ℂ)
    (a : (Fin n × Fin d → AF F) → ℂ) : thetaSum F (M.co.rho ψ w (c • a)) = c * thetaSum F (M.co.rho ψ w a) := by
  rw [rho_smul]
  unfold GlobalTheory.WeilM.thetaSum
  simp only [Pi.smul_apply, smul_eq_mul, tsum_mul_left]

theorem good_zero (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ) (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) :
    Good M ψ T 0 := by
  refine ⟨Submodule.zero_mem _, 0, Submodule.zero_mem _, fun x => ?_, fun w => ?_⟩
  · simpa only [map_zero, Pi.zero_apply] using hasDerivAt_const _ _
  · simp only [map_zero, rho_zero, GlobalTheory.WeilM.thetaSum, Pi.zero_apply, tsum_zero]
    exact hasDerivAt_const (0 : ℝ) (0 : ℂ)

theorem good_add (M : Model σ Y Wd) {ψ : AddChar (AF F) ℂ} (hψ : IsStd ψ)
    {T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)} (hT : ∀ t, ∀ Φ ∈ schA F (Fin n × Fin d), T t Φ ∈ schA F _)
    {a b : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) (hb : Good M ψ T b) : Good M ψ T (a + b) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  obtain ⟨hb, b', hb', hpb, htb⟩ := hb
  refine ⟨Submodule.add_mem _ ha hb, a' + b', Submodule.add_mem _ ha' hb', fun x => ?_, fun w => ?_⟩
  · simp only [map_add (f := _), Pi.add_apply]
    exact (hpa x).add (hpb x)
  · have e : (fun t => thetaSum F (M.co.rho ψ w (T t (a + b)))) =
        fun t => thetaSum F (M.co.rho ψ w (T t a)) + thetaSum F (M.co.rho ψ w (T t b)) := by
      funext t
      rw [map_add (f := _), theta_add M hψ w (hT t a ha) (hT t b hb)]
    rw [e, theta_add M hψ w ha' hb']
    exact (hta w).add (htb w)

theorem good_smul (M : Model σ Y Wd) (ψ : AddChar (AF F) ℂ)
    (T : ℝ → Module.End ℂ ((Fin n × Fin d → AF F) → ℂ)) (c : ℂ)
    {a : (Fin n × Fin d → AF F) → ℂ} (ha : Good M ψ T a) : Good M ψ T (c • a) := by
  obtain ⟨ha, a', ha', hpa, hta⟩ := ha
  refine ⟨Submodule.smul_mem _ c ha, c • a', Submodule.smul_mem _ c ha', fun x => ?_, fun w => ?_⟩
  · simpa only [map_smul, Pi.smul_apply, smul_eq_mul] using (hpa x).const_mul c
  · simpa only [map_smul, theta_smul] using (hta w).const_mul c

theorem schA_le_of_pure {κ : Type} [Fintype κ] {N : Submodule ℂ ((κ → AF F) → ℂ)}
    (h : ∀ (f : SInf F κ) (φ : ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB (κ → Fv F v)) →
      (∀ᶠ v in cofinite, φ v = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) → pure f φ ∈ N) :
    schA F κ ≤ N := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨f, g, hg, rfl⟩
  replace hg := GlobalTheory.SBSpan.mem_span_restrictedProd F _ g hg
  induction hg using Submodule.span_induction with
  | zero => rw [show pureA F f 0 = 0 from funext fun _ => mul_zero _]; exact N.zero_mem
  | add a b _ _ ha hb =>
    rw [show pureA F f (a + b) = pureA F f a + pureA F f b from funext fun _ => mul_add _ _ _]; exact N.add_mem ha hb
  | smul c a _ ha =>
    rw [show pureA F f (c • a) = c • pureA F f a from funext fun _ => mul_left_comm _ _ _]; exact N.smul_mem c ha
  | mem p hp =>
    obtain ⟨φ, hφ, hs, rfl⟩ := hp
    exact h f φ hφ hs

end GlobalTheory.ThetaInterchange

