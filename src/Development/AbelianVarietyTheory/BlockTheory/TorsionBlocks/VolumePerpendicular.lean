import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular

open NumberField MeasureTheory Formalism.BasicNotions Formalism.MainNotions.StandardLattice Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

def IsVol (D : D7) : letI := D.host.cmStar; HSpace D.host.E → ℕ → ℕ → ℝ → Prop :=
  letI := D.host.cmStar
  fun W P Q V =>
    0 < V ∧
    AllSome (IsVolMeas D W P Q) fun μ =>
    AllSome (fun 𝓕 => IsFundamentalDomain (HFinIn (AF D.host.F) D.sp.cm.sig W.gram) 𝓕 μ) fun 𝓕 =>
      μ 𝓕 = ENNReal.ofReal V

end GlobalTheory.IndefiniteRowSideFullHecke.VolumePerpendicular
