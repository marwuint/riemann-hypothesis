import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.OppositeColumnLifts
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.MatchingAdjoints
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ChainStepsAreGridArrows

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open GlobalTheory.Grid GlobalTheory.IndefiniteRowSideFullHecke.IwahoriMembership
open scoped Pointwise TensorProduct InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.FlipPath

variable {D : D7}

theorem isSelfDualC_sgn (ε : Bool) {S : HSp D} {Λ : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} (h : IsSelfDualC S Λ) :
    IsSelfDualC (sgn ε S) Λ := by
  cases ε
  · exact h
  · refine ⟨h.1, fun y => (h.2 y).trans (forall₂_congr fun x _ => ?_)⟩
    have e : ∑ i, ∑ j, star (x i) * (neg S).gram i j * y j = -∑ i, ∑ j, star (x i) * S.gram i j * y j := by
      simp [neg_gram, Finset.sum_neg_distrib]
    refine ⟨fun ⟨b, hb⟩ => ⟨-b, ?_⟩, fun ⟨b, hb⟩ => ⟨-b, ?_⟩⟩
    · refine Eq.trans ?_ e.symm
      rw [← hb]; simp
    · have := hb.trans e
      rw [← neg_eq_iff_eq_neg] at this
      rw [← this]; simp

section Fin

variable {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : Node D} {e : AE D} {P : Finset (Pl D.host.E)} {f₀ f : WO S.V T.V → ℂ}

theorem isFinVec_of_own {ε : Bool} (hv : IsVac ψ θ ε S T f₀) (hS : IsSelfDualC S.V S.Λ) (hT : IsSelfDualC T.V T.Λ) (he : IsIdemSum e P)
    {φ : Matrix (Fin T.V.rank) (Fin S.V.rank) (Datum.EAf D) → ℂ} (h : IsDatOwn ψ ε S T e f₀ φ f) : IsFinVec ψ θ ε S T f := by
  obtain ⟨hSB, ⟨Tm, hTm⟩, hall⟩ := h
  rw [hall Tm hTm]
  exact finVec_of_mem_span (S := sgn ε S.V) hv (GlobalTheory.Chain.StepVac.placeModel_span_ne hv.1 (isSelfDualC_sgn ε hS) hT
    (GlobalTheory.PlaceDatum.idemSum_mul_self he) he.2 (GlobalTheory.PlaceDatum.infPart_idemSum he) hTm hSB).1

end Fin

variable {G₀ : Type} [Group G₀] [Fintype G₀] {Pl0 T : Type} {A : FamIn D.what₂.LL G₀ Pl0 T D.R.m}
  {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] {R : RealDat D A Ks} (G : GridDat R)

end GlobalTheory.FlipPath

end
