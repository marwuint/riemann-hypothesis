import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.SideFam
import Development.AbelianVarietyTheory.Definitions.Jets.SumIoPr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.DerivedActionDiscreteSeriesProperties
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrechetContinuousContinuousOnOrbitHasDerivAt

open BranchingSupport Formalism.FourierDecayAlt Formalism.FourierDecayAlt.ThreeDimData Matrix MeasureTheory Finset
open scoped InnerProductSpace ENNReal

noncomputable section

namespace GlobalTheory.RawTens

def lm {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) : R.smSub →ₗ[ℂ] R'.smSub where
  toFun v := ⟨T v, h.mem v v.2⟩
  map_add' v w := Subtype.ext (h.add v v.2 w w.2)
  map_smul' a v := Subtype.ext (h.smul a v v.2)

@[simp] theorem lm_coe {k r : ℕ} {R R' : Rep k r} {T : R.H → R'.H} (h : SmMap R R' T) (v : R.smSub) :
    ((lm h v : R'.smSub) : R'.H) = T v := rfl

end GlobalTheory.RawTens
