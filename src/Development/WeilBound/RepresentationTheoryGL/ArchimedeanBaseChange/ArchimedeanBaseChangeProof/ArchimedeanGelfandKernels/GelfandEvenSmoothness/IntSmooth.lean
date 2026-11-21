import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.WaveSt

noncomputable section

open MeasureTheory Matrix Finset
open scoped ContDiff ComplexConjugate InnerProductSpace

namespace PositivityTheory.RgBcC.Mult

open PositivityTheory.RgTw (Mat G)
open PositivityTheory.RgBcC

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ}

def Hyp : Prop := LgFacts ∧ Unimod ∧ RCalc ∧ WaveSpeed ∧ WaveEx ∧ KerUniq ∧ KerOne

end PositivityTheory.RgBcC.Mult
