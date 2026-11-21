import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonemptyCuspFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjFsBasisOfUnitary
import Formalism.LocalToGlobal.ProjectiveLattices.FrameEx
import Formalism.LocalToGlobal.ProjectiveLattices.FrameExBor
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Formalism.LocalToGlobal.ProjectiveLattices.PetersonNormSubspace
import Formalism.LocalToGlobal.ProjectiveLattices.CompOrd
import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
import Formalism.LocalToGlobal.ProjectiveLattices.FreeBridge
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.PairUnfoldPfA
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.CabsDiagEqOne
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FrameMulTriangularOrthonormal
import Development.AbelianVarietyTheory.Proofs.TorusHaarMeasure.NormBcharMulNfacRmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace NumberField MeasureTheory Set
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.CxPts GlobalTheory.TopForm GlobalTheory.ChartGlue
open scoped ENNReal

namespace GlobalTheory

namespace CompHS

end CompHS

namespace CompHS

open ReciprocityTheory.ChartRestriction.G.FD
open GlobalTheory.AllWt (exOf wtOf lieFacZ modelWt homN)

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {Dw : Datum H} {l : Level H}
  {Xo : Moduli Dw l} {c : Coeff l}

section Fac

variable {r : ℕ} {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (x : ℝ)

open Classical in

def diagChar (e : Ix Dw → ℤ) (t : Ix Dw → (CAt σ)ˣ) : ℂ := toC (∏ ix, t ix ^ e ix).val

def homFac (la : AllWt.Weight Dw) (k : U.Comp) (w : (U.X k).dom) : ℝ :=
  lieFacZ Dw x (wtOf Dw la 0) * (U.X k).nfac (modelWt U (wtOf Dw la 0) k) w.1

theorem homN_eq_homFac (la : AllWt.Weight Dw) (f : Rul Xo c) (k : U.Comp) (w : (U.X k).dom) :
    homN U x (wtOf Dw la 0) f ⟨k, w.1⟩ = homFac U x la k w * ‖toC (evR Xo c f (U.un k w))‖ := by
  have e : rdU U f k w.1 = toC (evR Xo c f (U.un k w)) := dif_pos w.2
  change _ * (‖rdU U f k w.1‖ * (U.X k).nfac _ _) = _
  rw [e, homFac]
  ring

variable {U}

end Fac

end CompHS

end GlobalTheory
