import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GoodPartHasComplexCoordinates
import Formalism.LocalToGlobal.IndefiniteReal.BaseLiftsPackageOfPrimitiveLinks
import Formalism.LocalToGlobal.Divisibility.DivisionCompatibleToSub2Indef2
import Formalism.LocalToGlobal.IndefiniteReal.SpOfRwRange
import Formalism.LocalToGlobal.IndefiniteReal.EvalTieTOne
import Formalism.LocalToGlobal.IndefiniteReal.LinksStage
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowsJoinPinned
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowLevelMatch
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ChainTieAndV0Onto
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ColNormExistsImNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CxFactsOfPrims
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaMapReferenceTupleGoodPartOntoRows
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsReadOfMatrixTie
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsImNeZeroOfTotallyComplex
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ICCptEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CastGAMemGFset
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SeamExLinCpt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerEqIntegralOfAe
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GoodOperatorSpectrum

open Formalism.BasicNotions Formalism.L2.Indef Formalism.L2.DIV Formalism.IndefR.Cx Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.AutomorphicEvaluation Formalism.IndefR.Lev Formalism.L2.Theta NumberField MeasureTheory GlobalTheory.Mem.SJ Formalism.L2.SG.HidaSetting Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.RowDict Formalism.L2.SG.ColDict
open scoped InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.Mem.SJ.KernelJoin

theorem heq_of_reindex {K W Mem : Type} [Field K] (a : Mem → ℕ) {V : W → Type} [∀ u, AddCommGroup (V u)]
    [∀ u, Module K (V u)] {Z : Mem → Type} {Y : W → Type} (b : ∀ x, Fin (a x) → Z x) (g : ∀ u, V u → Y u)
    (w w' : W → Mem) (ν : ∀ u, (Fin (a (w u)) → K) ≃ₗ[K] V u) (ν' : ∀ u, (Fin (a (w' u)) → K) ≃ₗ[K] V u)
    (hw : w = w') (hν : HEq ν ν') (h : ∀ u i, HEq (b (w' u) i) (g u (ν' u (Pi.single i 1)))) :
    ∀ u i, HEq (b (w u) i) (g u (ν u (Pi.single i 1))) := by
  subst hw
  cases hν
  exact h

theorem smul_apply_eq_of_eq {A B : Type} [AddCommGroup B] [Module ℂ B] (f : A → B) {a a' : A} (h : a = a')
    (k κ : ℂ) {b : B} (hb : f a' = κ • b) : k • f a = (k * κ) • b := by
  rw [h, hb, mul_smul]

end GlobalTheory.Mem.SJ.KernelJoin
