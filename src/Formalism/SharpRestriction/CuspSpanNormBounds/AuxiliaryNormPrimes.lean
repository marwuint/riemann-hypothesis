import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.AuxiliaryNormPrimes

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Cnt NumberField Matrix Module
open scoped ENNReal NNReal InnerProductSpace

def TemperatureProductAsymptotic (D : D7) (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

section Loc

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def PlancherelBoundOneParameter (C' Cl Cg cb Cu cT CT C0 Cn C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stPT D large₂ C' Cl Cg cb Cu cT CT C0 Cn C1 C

end Loc

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def FamilyTemperatureProductAsymptotic (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => TemperatureProductAsymptotic (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Family

end Formalism.MainNotions.AuxiliaryNormPrimes
