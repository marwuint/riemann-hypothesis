import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.GlobAut
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GapAtLeast
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsReduction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntAfApproxInterUnitConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSelfDualHermitian
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExtIdMulSupNatCastConj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsProdLeOfIsRadical
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.AdelicLatticeSpec
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsPrimeIdempotentIntegralAdeles
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MulVecMemConjSmulOfAdjoint

open Formalism.MainNotions.S GlobalTheory.RowLev GlobalTheory.RowLev.Inhab NumberField IsDedekindDomain Matrix Formalism.UG
open scoped TensorProduct Classical

noncomputable section

namespace GlobalTheory.RowIndex

variable {I : AutInst}

def sigI (I : AutInst) : IntAf I.F I.E →+* IntAf I.F I.E :=
  ((sigR I.cm.sig (Af I.F)).comp (IntAf I.F I.E).subtype).codRestrict _ fun z =>
    (intAf_approx_inter_unit_conj I 1 le_rfl).2.2.2 z.1 z.2

theorem coe_sigI (z : IntAf I.F I.E) : (sigI I z : I.E ⊗[I.F] Af I.F) = sigR I.cm.sig (Af I.F) z := rfl

def hI (x y : I.Lf) : IntAf I.F I.E :=
  ⟨hAf I x y, (GlobalTheory.AdelicLattice.adelicLattice_selfDual I y).1 y.2 x x.2⟩

theorem coe_hI (x y : I.Lf) : (hI x y : I.E ⊗[I.F] Af I.F) = hAf I x y := rfl

end GlobalTheory.RowIndex
