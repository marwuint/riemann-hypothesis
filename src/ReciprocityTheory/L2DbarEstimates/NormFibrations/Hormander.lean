import ReciprocityTheory.L2DbarEstimates.JacobianInterpolationStatement
import ReciprocityTheory.L2DbarEstimates.NormFibrations.Imports
import ReciprocityTheory.L2DbarEstimates.ChartDerivatives.TsupportDbSubset
import ReciprocityTheory.L2DbarEstimates.Mollifiers.HasCompactSupport
import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollEnormSqLe
import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollTendstoOfContinuous
import ReciprocityTheory.L2DbarEstimates.Mollifiers.FderivMollApply
import ReciprocityTheory.L2DbarEstimates.Mollifiers.MollGraph
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.MvDivIntegrand
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ExtNull
import ReciprocityTheory.L2DbarEstimates.WeakHolomorphy.ImportsAlt
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.CvxOfConvex
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.MinimalSolution
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.HormanderLemma
import ReciprocityTheory.L2DbarEstimates.MinimalSolutions.OntoWithBoundTop
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.BasicIdentityStatement
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HalfSumNormSubSq
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportDTw
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.WIbpLeft
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsBis
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.ImportsTer
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.HasCompactSupportOfVanish
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.TstarNormSq
import ReciprocityTheory.L2DbarEstimates.BasicIdentity.Imports
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.HStatementOf
import ReciprocityTheory.L2DbarEstimates.HormanderEstimate.Closed
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.Matrix
import ReciprocityTheory.L2DbarEstimates.SkodaWeights.VolProdFinApply
import ReciprocityTheory.L2DbarEstimates.LeviForms.TwBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.Bergman
import ReciprocityTheory.L2DbarEstimates.LeviForms.BasicExpBound
import ReciprocityTheory.L2DbarEstimates.LeviForms.AddLogPosOfThreeQuartersLe
import ReciprocityTheory.L2DbarEstimates.LeviForms.Cutoff
import ReciprocityTheory.L2DbarEstimates.LeviForms.PolarBallReal
import ReciprocityTheory.L2DbarEstimates.LeviForms.CovDet
import ReciprocityTheory.L2DbarEstimates.LeviForms.ShellA
import ReciprocityTheory.L2DbarEstimates.LeviForms.Vanish
import ReciprocityTheory.L2DbarEstimates.LeviForms.FxExpNegWgtLeShell
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetMonoDetOneAdd
import ReciprocityTheory.L2DbarEstimates.LeviForms.DetUpdateColEq
import ReciprocityTheory.L2DbarEstimates.LeviForms.ImportsAlt

universe u

namespace ReciprocityTheory.L2DbarEstimates

open MeasureTheory

theorem regMAll (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : F.RegMStatement n M :=
  F.regM n M C.reg (F.extend n M)

theorem hormander (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : HStatement n M :=
  F.hStatement_of n M (E.ap n M) (E.tStarIbp n M) (chain n M) C.reg
    (B.moll_graph (V n) volume ℝ) (B.moll_smooth (V n) volume) (B.moll_support (V n) volume)
    (B.kernel_std (V n) volume)

theorem skoda (n : ℕ) (M : Type*) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : SStatement n M :=
  H.skoda n M (fun p => hormander n (M × Fin p))
    (fun p => F.needBergmanClosed n (M × Fin p) (regMAll n (M × Fin p)))

theorem tw (n : ℕ) (M : Type u) [TopologicalSpace M] [T2Space M]
    [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] : TWStatement n M :=
  I.tw n M (hormander n M) (F.holoClosedNeed n M (regMAll n M))

end ReciprocityTheory.L2DbarEstimates
