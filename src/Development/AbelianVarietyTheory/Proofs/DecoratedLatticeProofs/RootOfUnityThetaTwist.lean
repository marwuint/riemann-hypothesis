import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.QLev
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ProdDat
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilDataDifferBySplittingFactorQuotient
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EvalAtOneExtremalMul
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SplitPart
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.SplitLastBlockActX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeCharEqOneOfTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IdelicCharacterPowEqOneFiniteIdelesOfOrderDvd
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OpenKernelIdeleCharacterTrivialFinitePartOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsDetRootFinPartOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsIsDetRoot
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.NormEmbeddingHostFormConstantEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConstRelIffTwistFactorAt
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SeeSaw GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.LocMod GlobalTheory.MiS ValuativeRel
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Fam
set_option maxHeartbeats 1000000

noncomputable section

namespace GlobalTheory.TupRoot

variable {D : D7}

theorem finite_pow_eq_one (n : ℕ) (hn : 0 < n) : {z : Circle | z ^ n = 1}.Finite := by
  refine ((Polynomial.nthRoots n (1 : ℂ)).toFinset.finite_toSet.preimage
    (Set.injOn_of_injective Circle.coe_injective)).subset fun z hz => ?_
  simp only [Set.mem_preimage, Finset.mem_coe, Multiset.mem_toFinset, Polynomial.mem_nthRoots hn]
  have hz' : z ^ n = 1 := hz
  have := congrArg (fun w : Circle => (w : ℂ)) hz'
  simpa using this

theorem isOpen_ker_of_pow {X : Type} [TopologicalSpace X] [Group X] (c : X →* Circle) (hc : Continuous c) (n : ℕ) (hn : 0 < n)
    (hp : ∀ x, c x ^ n = 1) : IsOpen (c.ker : Set X) := by
  have hF : ({z : Circle | z ^ n = 1} \ {1}).Finite := (finite_pow_eq_one n hn).diff
  have ho := hF.isClosed.isOpen_compl.preimage hc
  convert ho using 1
  ext x
  simp [hp x]

theorem pow_eq_one_of_chrEq {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ}
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) : c x ^ n = 1 := by
  have := GlobalTheory.HeckeFinTrivial.eq_one_of_trivial_on_finite D ((powMonoidHom n).comp c)
    ⟨(continuous_pow n).comp h.1.1, fun k => by
      have := h.1.2 k
      simp only [MonoidHom.coe_comp, Function.comp_apply, powMonoidHom_apply]
      erw [this, one_pow]⟩
    (fun y hy => by simpa using _root_.GlobalTheory.CharOrderFin.char_pow_eq_one_of_orderDvd D c χ h n hn y hy) x
  simpa using this

theorem eq_one_of_finPart {c : (AE D)ˣ →* Circle} {χ : Formalism.L2.Host.HChar D.host.E} (h : ChrEq c χ) {n : ℕ} (hn0 : 0 < n)
    (hn : χ.OrderDvd n) (x : (AE D)ˣ) (hx : finPart D (x : AE D) = 1) : c x = 1 :=
  GlobalTheory.UnivCover.OpenKerChar.map_eq_one_of_finPart_eq_one D c
    (isOpen_ker_of_pow c h.1.1 n hn0 (pow_eq_one_of_chrEq h hn)) x hx

theorem twist_eq {S T : HSp D} {ψ : AddChar (AF D.host.F) ℂ} {χS χT ν : (AE D)ˣ →* Circle}
    {om om' : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    (hW' : IsWeilDatumO ψ S T (χS * ν) (χT * ν) om') {g : GA D S} {h : GA D T} {x y : (AE D)ˣ}
    (hx : IsDetRoot S g x) (hy : IsDetRoot T h y) {f : WO S T → ℂ} (hf : IsThetaFunO ψ S T f) :
    om' (g, h) f = (((ν x)⁻¹ * ν y : Circle) : ℂ) • om (g, h) f := by
  rw [_root_.GlobalTheory.WeilChange.weilData_differ_by_splitFac D ψ S T χS χT _ _ om om' hW hW' g h x y hx hy f hf]
  congr 1
  have e : splitFacO (χS * ν) (χT * ν) x y = (ν x)⁻¹ * ν y * splitFacO χS χT x y := by
    simp only [splitFacO, MonoidHom.mul_apply]
    rw [mul_inv]
    ac_rfl
  rw [e, Circle.coe_mul, mul_assoc, mul_inv_cancel₀ (Circle.coe_ne_zero _), mul_one]

theorem isWeil_rec {ψ : AddChar (AF D.host.F) ℂ} {χS χT : (AE D)ˣ →* Circle} {n n' : ℕ} (e : n = n')
    (om : Om (Yc D n) D.sp.X') (h : IsWeilDatumO ψ (Yc D n) D.sp.X' χS χT om) :
    IsWeilDatumO ψ (Yc D n') D.sp.X' χS χT (Eq.rec (motive := fun n _ => Om (Yc D n) D.sp.X') om e) := by
  subst e
  exact h

end GlobalTheory.TupRoot

