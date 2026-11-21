import Mathlib
import Formalism.LocalToGlobal.KernelLattices.ColumnData
import Formalism.LocalToGlobal.KernelLattices.ColumnData.StdOKP
import Formalism.LocalToGlobal.KernelLattices.ColumnData.BaseLinkOfNonzeroDelta
import Formalism.LocalToGlobal.KernelLattices.ColumnData.Smooth
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst

open NumberField IsDedekindDomain MvPolynomial

noncomputable section

namespace Formalism.L2.Ker.Cd

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Host Formalism.FrobeniusOrbits

theorem Base.stdOK {D : Car} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (hcc : TaylorLogMetric.IsCurveIdeal D cc)
    (hδ : TaylorLogMetric.IsDiscriminantTwelfthRootOfIdealLattice D cc δ) : B.StdOK :=
  Formalism.L2.Ker.Cd.IntegralLatticeDensity.SO.stdOK B hcc hδ

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Host Formalism.FrobeniusOrbits

end Formalism.L2.Ker.Cd
