import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasTypeVec
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.LabesseWaldspurger
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ConstantTermVanishing
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspidalNoRadicalFixed
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.StandardMaximalParabolic
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HasOrbIntTensorOfHasOrbInt
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeightedOrbitalIntegralTypeTestVanish
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.SplitInclMemExtSubIff

open MeasureTheory Set Filter NumberField IsDedekindDomain
open GlobalTheory.AdelicU GlobalTheory.OpTrace GlobalTheory.Orb GlobalTheory.AutomorphicL2Unitary GlobalTheory.AutMult Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.IndefR.Mult
open GlobalTheory.IndefiniteRowSideFullHecke.PlusPolynomialRoots (IsTestData PPol Tor Phi PhiOK PhiReal ellKernel Gap NoFixed IsLatticeConj GeomExpansion EllipticPart TraceEq)
open GlobalTheory.PRep (IsAdmissible)
open GlobalTheory.TrMult
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Chamber GlobalTheory.TruncKer GlobalTheory.Cusp

noncomputable section

namespace GlobalTheory.TypesFactor

section Split

variable {ι : Type} [DecidableEq ι] (i : ι) (G : ι → Type) [∀ j, Group (G j)] [∀ j, TopologicalSpace (G j)]

def splitEquiv : (∀ j, G j) ≃ₜ* G i × ∀ j : {j // j ≠ i}, G j :=
  { Homeomorph.piSplitAt i G with map_mul' := fun _ _ => rfl }

variable {i G}

theorem splitEquiv_apply (x : ∀ j, G j) : splitEquiv i G x = (x i, fun j : {j // j ≠ i} => x j) := rfl

end Split

end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor
end GlobalTheory.TypesFactor

namespace GlobalTheory.TypesFactor

end GlobalTheory.TypesFactor
