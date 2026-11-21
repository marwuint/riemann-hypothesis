import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.DataParams₂
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsPrimitiveSub
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianLattices.StatementMass
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds

noncomputable section

namespace Formalism.MainNotions.VanishingOnXAndXPlusMass

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ)

open NumberField Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Conclusion₂

variable (D : D7)

def Conclusion1 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C c : ℝ) : Prop :=
  UnitaryVolumeMass.stX D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C c

def PointsLemma (u : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stLem3L0 D u

end Conclusion₂

section admitted

variable (D : D7)

def adm1 : Prop :=
  UnitaryVolumeMass.stMassRatio D

end admitted

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def Conclusion3Family : Prop := ∀ x, Fm.x1 < x → ∀ (i : Fm.Ix x) u, PointsLemma (Fm.D x i) u

end Family

end Formalism.MainNotions.VanishingOnXAndXPlusMass

end
