import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.LogDerivativeJetsIntegral
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.JetsInOfOneVariable
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.UnitKer
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtPower
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.EtJets
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensZEt
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.TensorFourthPowerScaling
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.ScalarConst
import Formalism.LocalToGlobal.AlgebraicTheory.AlgebraicTheoryProofs.DvdOfNormIntCastLt
import Formalism.LocalToGlobal.AlgebraicTheory.StatementStep
import Formalism.LocalToGlobal.Divisibility.JetBounds.Statement
import Formalism.LocalToGlobal.Divisibility.JetBounds.MinorProductsLattice
import Formalism.GaussJetBounds.FinalB
import Formalism.LocalToGlobal.Divisibility.JetBounds.JetBoundsProofs.NormEqOneOfNotMem
import Mathlib
import Formalism.LocalToGlobal.ExponentGrids.IntegerShiftClosedExponent
import Formalism.QuotientMetricDivisors.Complement2Normaliser
import Formalism.TranslateCocycles.StatementHC
import Formalism.SizeWindowBrackets.SlopesFromSizeAndCount
import Formalism.LocalRingCardinality.DataErr
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.LocalToGlobal.ExponentGrids.ExponentGridsProofs.NormaliserValuationBound
import Formalism.SizeWindowBrackets.ChainSlopeWindows.PBrDiv
import Formalism.LocalToGlobal.Divisibility.NumbersLemmas
import Formalism.LocalToGlobal.AlgebraicTheory.StatementKer
import ReciprocityTheory.ReductiveGroups.LatticeEmbeddings.IotaPlace

namespace Formalism.L2.AlgTh

theorem logDerJets : LogDerJets := log_derivative_jets_integral
theorem powLogDer : PowLogDer := power_log_derivative_jets
theorem prodScaleJets : ProdScaleJets := product_scaling_jets
theorem linScale : LinScale := linear_scaling_jets
theorem unitKerInt : UnitKerInt := unit_kernel_integral_coords
theorem etPower : EtPower := etPower_of unitKerInt
theorem etJetsSigma : EtJetsSigma := etJetsSigma_of etPower logDerJets powLogDer
theorem etJetsTh0 : EtJetsTh0 := etJetsTh0_of etJetsSigma
theorem etThetaZ : EtThetaZ := etThetaZ_of etJetsTh0 prodScaleJets
theorem tensZEt : TensZEt := tensor_integral_torsion
theorem etLoc : EtLoc := etLoc_of tensZEt etThetaZ linScale
theorem scalarConst : ScalarConst := scalar_constant_value
theorem xiSwap : XiSwap := xi_swap
theorem xiEt : XiEt := xiEt_of etLoc

end Formalism.L2.AlgTh
