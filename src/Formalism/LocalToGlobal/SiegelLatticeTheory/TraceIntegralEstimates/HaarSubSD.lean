module

public import Formalism.LocalToGlobal.SiegelLatticeTheory.TraceIntegralEstimates.HaarSubS
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NGClosed
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.SynthesizedVectorZPairing
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ConjHSymmApply
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom
public import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.GramEqOfHyp
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.InHHDef
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact
import Mathlib.Algebra.Order.Floor.Extended
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Algebra.Order.Interval.Basic
import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
import Mathlib.Analysis.Normed.Algebra.GelfandRadius
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
import Mathlib.RingTheory.Radical.NatInt
import Mathlib.Tactic.Basify
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
import Mathlib.Topology.Sheaves.Init

@[expose] public section

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.MainNotions.S Matrix

namespace Formalism.L2.S.Pv.HaarSubS

open Formalism.L2.SG.HidaSetting Formalism.L2.SG.RealObj Formalism.L2.SG.RealObj.InfCut Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem frm_at {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (v : InfinitePlace X.B.I.F) :
    ∃ w : Fin D.R.k → Fin X.B.I.n → ℂ, NilradicalHermitianFrames.NH.Frm (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) w (Tw u) := by
  have hdim : X.B.I.n = 2 * D.R.rS + 1 + D.R.k := (Formalism.L2.SG.Pf.card_frame X).symm
  have hsig := Formalism.L2.SG.PoincareInHH.Cut.card_eps_false X v
  have hpos : 0 < Tw u := by
    unfold Tw
    exact_mod_cast (D.mem u).A.T_prime.pos
  have hee : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.eR b)) = 0 :=
    fun a b => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ee]; simp)
  have hez : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) = 0 :=
    fun a => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [(X.zu_orth u a).1]; simp)
  have hzz : hJ (X.B.I.ε v) (rv X.B.I v (X.zR u)) (rv X.B.I v (X.zR u)) = -(Tw u : ℂ) :=
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.zu_norm u]; simp [Tw])
  have hep : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.eR a)) (rv X.B.I v (X.fR b)) = if a = b then 1 else 0 :=
    fun a b => (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ef]; split_ifs <;> simp)
  have hpp : ∀ a b, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.fR b)) = 0 := fun a b =>
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [X.ff]; simp)
  have hpz : ∀ a, hJ (X.B.I.ε v) (rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) = 0 := fun a =>
    (Formalism.L2.SG.PoincareInHH.Cut.hJ_crd X v _ _).trans (by rw [(X.zu_orth u a).2]; simp)
  obtain ⟨w, hww, hew, hpw, hzw⟩ := UnitaryIsometries.RI.complement (X.B.I.ε v) hdim hsig hpos
    (⟨hee, hep, hpp, hez, hpz, hzz⟩ : UnitaryIsometries.RI.Hyp (X.B.I.ε v) _ _ _ _)
  exact ⟨w, ⟨hee, hep, hpp, hez, hpz, hzz, hew, hpw, hzw, hww, hpos.ne'⟩⟩

theorem mem_Hu_iff {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) (s : X.B.I.Ginf) :
    s ∈ Hu X u ↔ ∀ v, s v ∈ NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
      (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) := by
  constructor
  · intro hs v
    refine ⟨fun a => hs v _ ?_, fun a => hs v _ ?_, hs v _ ?_⟩
    · exact Or.inl (Or.inl ⟨a, rfl⟩)
    · exact Or.inl (Or.inr ⟨a, rfl⟩)
    · exact Or.inr rfl
  · intro hs v x hx
    rcases hx with (⟨a, rfl⟩ | ⟨a, rfl⟩) | hx
    · exact (hs v).1 a
    · exact (hs v).2.1 a
    · rw [Set.mem_singleton_iff] at hx
      subst hx
      exact (hs v).2.2

theorem Hu_eq_pi {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (u : D.what₂.Word) : Hu X u = Set.pi Set.univ (fun v => (NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a))
    (fun a => rv X.B.I v (X.fR a)) (rv X.B.I v (X.zR u)) : Set (Formalism.REAL.UJ (X.B.I.ε v)))) := by
  ext s
  rw [mem_Hu_iff]
  simp

theorem sDecomp_holds : SDecomp := by
  intro D X u
  have hw := fun v => frm_at X u v
  choose w Fw using hw
  have hdim : ∀ v : InfinitePlace X.B.I.F, X.B.I.n = 2 * D.R.rS + 1 + D.R.k := fun _ => (Formalism.L2.SG.Pf.card_frame X).symm
  set SGv := fun v => UnitaryIsometries.RI.SG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) with hSGv
  set NGv := fun v => NilradicalHermitianFrames.NH.NG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (rv X.B.I v (X.zR u)) with hNGv
  set HGv := fun v => NilradicalHermitianFrames.NH.HG (X.B.I.ε v) (fun a => rv X.B.I v (X.eR a)) (fun a => rv X.B.I v (X.fR a))
    (rv X.B.I v (X.zR u)) with hHGv
  have hS : ∀ s, s ∈ X.SinfU u ↔ ∀ v, s v ∈ SGv v := fun s => Iff.rfl
  have hN : ∀ s, s ∈ X.NinfU u ↔ ∀ v, s v ∈ NGv v := fun s => Iff.rfl
  have hH : ∀ s, s ∈ Hu X u ↔ ∀ v, s v ∈ HGv v := mem_Hu_iff X u
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have he : X.SinfU u = ⋂ v, (fun s : X.B.I.Ginf => s v) ⁻¹' (SGv v : Set _) := by
      ext s
      simpa only [Set.mem_iInter, Set.mem_preimage, SetLike.mem_coe] using hS s
    rw [he]
    exact isClosed_iInter fun v => (UnitaryIsometries.RI.SG_closed _ _ _).preimage (continuous_apply v)
  · exact (hS 1).2 fun v => (SGv v).one_mem
  · exact fun a ha b hb => (hS _).2 fun v => (SGv v).mul_mem ((hS a).1 ha v) ((hS b).1 hb v)
  · exact fun a ha => (hS _).2 fun v => (SGv v).inv_mem ((hS a).1 ha v)
  · exact (hN 1).2 fun v => (NGv v).one_mem
  · exact fun a ha b hb => (hN _).2 fun v => (NGv v).mul_mem ((hN a).1 ha v) ((hN b).1 hb v)
  · exact fun a ha => (hN _).2 fun v => (NGv v).inv_mem ((hN a).1 ha v)
  · rw [Hu_eq_pi]
    exact isCompact_univ_pi fun v => NilradicalHermitianFrames.NH.HG_compact (Fw v) (hdim v)
  · exact (hH 1).2 fun v => (HGv v).one_mem
  · exact fun a ha b hb => (hH _).2 fun v => (HGv v).mul_mem ((hH a).1 ha v) ((hH b).1 hb v)
  · exact fun a ha => (hH _).2 fun v => (HGv v).inv_mem ((hH a).1 ha v)
  · intro h hh n hn
    exact (hN _).2 fun v => NilradicalHermitianFrames.NH.conj_mem _ _ _ _ ((hH h).1 hh v) ((hN n).1 hn v)
  · intro n hn h hh
    exact (hS _).2 fun v => (SGv v).mul_mem (NilradicalHermitianFrames.NH.NG_le_SG _ _ _ ((hN n).1 hn v))
      (NilradicalHermitianFrames.NH.HG_le_SG _ _ _ _ ((hH h).1 hh v))
  · intro s hs
    have hdec := fun v => NilradicalHermitianFrames.NH.mem_NH (Fw v) (hdim v) ((hS s).1 hs v)
    choose m hm h hh heq using hdec
    exact ⟨m, (hN m).2 hm, h, (hH h).2 hh, funext heq⟩

end Formalism.L2.S.Pv.HaarSubS
