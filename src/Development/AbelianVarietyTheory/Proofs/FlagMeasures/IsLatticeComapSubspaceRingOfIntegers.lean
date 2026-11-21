import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.HermitianLattices.FinalNeighbourConstruct
import Formalism.HermitianLattices.HermitianLatticesProofs.ClassSetAssembly
import Formalism.HermitianLattices.HermitianLatticesProofs.GenusCovolBound
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.TermLoc
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.LocClosed
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsLatticeComapSubtype

open scoped Classical ENNReal
open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.Full Formalism.L2.SG.RowsConc Formalism.L2.SG.NGData Formalism.L2.SG.TermLoc GlobalTheory.Unfold
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory

theorem isLattice_comap_subtype_ringOfIntegers {K V : Type} [Field K] [NumberField K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
    (Λ : Submodule (𝓞 K) V) (hΛ : Submodule.IsLattice K Λ) (W : Submodule K V) :
    Submodule.IsLattice K (Λ.comap (W.subtype.restrictScalars (𝓞 K))) := by
  first
  | exact @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype
  | (apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SmulMemComapLattice.isLattice_comap_subtype ..)

end GlobalTheory
