import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.EigenvalueSeparation.FaceMapCompSuccAboveCastSucc
import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.PIndMapA

noncomputable section

open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation

namespace PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

section Pair

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {a b : ℕ}

theorem pairSpace_eq_tens2 (U₁ : Submodule ℂ (Sm E a)) (U₂ : Submodule ℂ (Sm E b)) :
    pairSpace U₁ U₂ = tens2 U₁ U₂ := rfl

end Pair

inductive Shape : ℕ → Type
  | leaf (N : ℕ) : Shape N
  | node {r s : ℕ} : Shape r → Shape s → Shape (r + s)

end PositivityTheory.Rg.BcB.SpectralAccumulation.Glue

end
