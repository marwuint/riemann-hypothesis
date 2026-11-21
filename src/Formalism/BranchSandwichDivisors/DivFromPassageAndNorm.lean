import Formalism.BranchSandwichDivisors.StatementL
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.ReductionLemmaFirst
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchScale
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.BranchMap
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.XiNorm
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MemBranchRangeOfDefectEq
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.GoodDual
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Interlace
import Mathlib
import Formalism.QuotientMetricDivisors.StatementK
import Formalism.BranchSandwichDivisors.StatementR
import Formalism.QuotientMetricDivisors.HermitianTwistDivisors.TheoremDivIneq
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.MapScale
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Numeric
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.OrthSum
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.Transfer
import Formalism.BranchSandwichDivisors.BranchIsometryProofs.TransferMean

namespace Formalism.BranchingDeterminantCap

theorem mapMu : MapMu := map_slope_mu
theorem scaleSandwich : ScaleSandwich := scale_sandwich_bound
theorem orthSum : OrthSum := orthogonal_sum_slope
theorem powMu : PowMu := power_slope_mu
theorem orthSandwich : OrthSandwich := orthogonal_sandwich_bound
theorem transferPart : TransferPart := transferPart_of mapMu powMu
theorem transferMuMax : TransferMuMax := transferMuMax_of scaleSandwich orthSum powMu
theorem transferDeg : TransferDeg := degreeTransferBound
theorem interlaceIdent : InterlaceIdent := interlaceIdentities
theorem capConst : CapConst := capacity_constant_bound
theorem weylDimBound : WeylDimBound := weyl_dimension_bound
theorem branchMap : BranchMap := branch_map_formula
theorem xiNorm : XiNorm := xi_norm_bound

end Formalism.BranchingDeterminantCap
