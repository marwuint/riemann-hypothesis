import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ReadsHecke
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IrreducibleWeightDescendsToPolynomialModule
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeightMatricesMatchOfCoeffSpaceIso
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MatchingMatricesOfBaseChangeRepresentation
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut NumberField IsDedekindDomain GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.GroupRetwisting GlobalTheory.Mem.Top.Bl GlobalTheory.Mem.R3 GlobalTheory.Mem.R3.Rw GlobalTheory.HeightCounting GlobalTheory.HeightCounting.Up
open Formalism.AUTREP (GAf)
open Neutral.B1 (Ideles)
open GlobalTheory.HeckeGal (Gab IsGlobalArtin)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000
open GlobalTheory.LevCmp
open GlobalTheory.TwistChoice (Reading ReadsAt)

noncomputable section
namespace GlobalTheory.LevCmp
open Formalism.L2.DIV GlobalTheory.CoefModel

section Gen2
variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

theorem match_mtwRat (γ : GQ L n) : (((γ : GAf L n) : GL (Fin n) (ReciprocityTheory.Aut.AL L)) : Matrix (Fin n) (Fin n) (ReciprocityTheory.Aut.AL L)) =
    ((Formalism.L2.Col.mtwRat γ : GL (Fin n) L) : Matrix (Fin n) (Fin n) L).map Algebra.TensorProduct.includeLeftRingHom :=
  (congrArg Units.val (Formalism.L2.Col.mtwInc_mtwRatFun γ)).symm

theorem domWeight_ext {N : ℕ} {a b : DomWeight N} (h : a.w = b.w) : a = b := by
  cases a; cases b; subst h; rfl

end Gen2

end GlobalTheory.LevCmp

end
