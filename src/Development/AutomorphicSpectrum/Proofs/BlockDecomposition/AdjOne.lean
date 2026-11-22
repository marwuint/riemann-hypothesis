import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.UnitarySchrodingerModel.DictKAOfParts
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsSelfDualSiegelWeilMeasures

noncomputable section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)

namespace GlobalTheory.CompanionTheory.MM
open GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC GlobalTheory.CompanionTheory.IwaAd PositivityTheory.PfSWUS GlobalTheory.CompanionTheory.SiegelND

variable {D : D7} {n : ℕ}

def pull (a : GL (Fin n) (AE D)) (b : hermA D n) : hermA D n :=
  ⟨(a⁻¹).1 * b.1 * adj (a⁻¹).1, by
    have hb : adj b.1 = b.1 := b.2
    change adj _ = _
    rw [adj_mul, adj_mul, adj_adj, hb, Matrix.mul_assoc]⟩

end GlobalTheory.CompanionTheory.MM
