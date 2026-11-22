import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BcrisFrobeniusFixedFilZeroEqQp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FundamentalMapSurjective
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BcrisRegularOfTensorInj
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AlgClosureTensorBcrisToBdRInjective

noncomputable section

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.MemLoc
open scoped Formalism.Per

namespace GlobalTheory.Published

theorem FontaineBcris.fund_holds (l : ℕ) [Fact l.Prime] (C : Core l) : C.Fund := by
  intro b h1 h2
  exact GlobalTheory.MemLoc.fundamental_exact l C b h1 h2

theorem FontaineBcris_holds : FontaineBcris :=
  FontaineBcris.of_rest fun l _ C =>
    ⟨_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C, FontaineBcris.fund_holds l C, GlobalTheory.MemLoc.FundOnto.fundOnto l C,
      _root_.GlobalTheory.MemLoc.regular_of_tensorInj l C (_root_.GlobalTheory.MemLoc.TensorInj.tensorInj l C)⟩

end GlobalTheory.Published
