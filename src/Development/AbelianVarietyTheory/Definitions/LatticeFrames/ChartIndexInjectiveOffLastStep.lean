import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.LevChiEqOne
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotTopPtOne
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IsPointOfDecoratedLatticeUnique

noncomputable section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Forms Formalism.L2.Ker
open NumberField IsDedekindDomain Matrix MeasureTheory GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.MixPer GlobalTheory.KJInf GlobalTheory.SeeSaw
open scoped TensorProduct Classical

namespace GlobalTheory.AdForm.TwTest
attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {B : Base} {X : PreX B.toPre} {I : TC B X} {l : I.Laws} {Z : TC.Later B (I.cols l)} {u : B.Word} {a : I.ι} {Ch : ℕ → Type}
  {A : TwDat I l Z u a Ch}

theorem cosetIn_eq_empty {j : ℕ} (h : j + 1 ≠ B.R.m) (p : PtAt B.R I.sel (I.tup a) (I.cst a) u j) : cosetIn p = fun _ => ∅ := by
  have h1 : p.1.2 = ∅ := by
    have := p.2
    rw [ysAt_ys_of_ne I.sel (I.tup a) (I.cst a) h] at this
    exact this
  funext P
  ext z
  simp [cosetIn, h1]

theorem chartIndex_injective_offLastStep (hA : A.Is) {j : ℕ} (hj : j ≤ B.R.m) (h : j + 1 ≠ B.R.m) : Function.Injective (A.b0 j) := fun α β e =>
  hA.chart_ext j hj α β e (by rw [cosetIn_eq_empty h, cosetIn_eq_empty h])

theorem subsingleton_top (hA : A.Is) : Subsingleton (Ch B.R.m) :=
  ⟨fun α β => chartIndex_injective_offLastStep hA le_rfl (by omega) (by rw [Idx.eq_top (A.b0 _ α) le_rfl, Idx.eq_top (A.b0 _ β) le_rfl])⟩

end GlobalTheory.AdForm.TwTest
