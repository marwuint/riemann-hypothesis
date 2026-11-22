import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalShareSumBound
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.ToKnownTheoremsOf

section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.CovTop.LocShareNum
open Formalism.MainNotions.ArithmeticCylinders (admLq TieAdmG eUk eJk locShare goodAt VecAt IsLabel)
open Formalism.L2.GlobalTheoryTheory.ConcN (Wg SizesRec SizesAt weight_numbers_bound)
open Formalism.L2.GlobalTheoryTheory.ConcNWeight (RangeW host_facts sum_wtOf eUk_coeff_one_re_pos eJk_coeff_one_re_pos wtOf_eq_zero_of_not_label rangeW_of_sizes)
local instance {D : D7} (k : Fin 2) : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
local instance {D : D7} (k : Fin 2) : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
end GlobalTheory.CovTop.LocShareNum
namespace GlobalTheory.CovTop.LocShareNum
end GlobalTheory.CovTop.LocShareNum
end
end

