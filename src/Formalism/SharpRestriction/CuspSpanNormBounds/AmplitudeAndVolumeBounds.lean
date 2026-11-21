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

namespace Formalism.MainNotions.VanishingOnXAndXPlus

export Formalism.MainNotions.S.UnitaryVolumeMass (embU succMin dualZ ForAmpH absMinor)

open NumberField Matrix Module Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt
open scoped ENNReal NNReal InnerProductSpace

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section B3

variable (D : D7)

abbrev Stand (u u' : D.what₂.Word) : Prop := Cnt.Stand D u u'

abbrev Hyp0 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop := Cnt.Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0

end B3

section Lat

variable (D : D7)

def adm14 (u u' : D.what₂.Word) : Prop :=
  UnitaryVolumeMass.stThmAAt D u (Tu D u')

end Lat

section Lines

variable (D : D7)

def adm6 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 δ : ℝ) : Prop :=
  UnitaryVolumeMass.stTprod D large₂ C' Cl Cg cb Cu cT CT C0 δ

def adm7 (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  UnitaryVolumeMass.stTcritLow D large₂ C' Cl Cg cb Cu cT CT C0

def adm8 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  UnitaryVolumeMass.stForm D large₂ u u' C' Cl Cg cb Cu cT CT C0 A

def PlaneWaveLetters : Prop :=
  UnitaryVolumeMass.stWeyl D

def PlaneWaveIsometry (large₂ : SizeData₂ D) (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 →
    ∀ (w : D.what₂.Word) (τ : D.what₂.Tau),
      (dimPiU D.R.k (uS D w τ) : ℝ) = vand (uS D w τ) / ∏ i ∈ Finset.range D.R.k, (i.factorial : ℝ)

end Lines

section Counts

variable (D : D7)

def ArchimedeanSignatureMatching (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stSW D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

def adm20 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A Ad C : ℝ) : Prop :=
  UnitaryVolumeMass.MeanFlagPairCount D large₂ u u' C' Cl Cg cb Cu cT CT C0 A Ad C

def adm21 (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.PartnerCountBound D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end Counts

section Amp

open MeasureTheory Finset Formalism.QuantumDeterminants

variable (D : D7) (large₂ : SizeData₂ D)

def adm22 (C' Cl Cg cb Cu cT CT C0 _A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stCONST D large₂ C' Cl Cg cb Cu cT CT C0 C1 C

def L2HilbertSchmidtPointwise (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.L2PointwiseLoss D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def L2LossProductBound (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stL2prod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def OperatorNormPointwiseBound (C' Cl Cg cb Cu cT CT C0 A C1 C : ℝ) : Prop :=
  UnitaryVolumeMass.stABS D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C

def AbsoluteConvergenceBesselIntegral (C' Cl Cg cb Cu cT CT C0 A C1 : ℝ) : Prop :=
  UnitaryVolumeMass.stABSconv D large₂ C' Cl Cg cb Cu cT CT C0 A C1

def AbsoluteLossProductBound (C' Cl Cg cb Cu cT CT C0 A C C2 Ch : ℝ) : Prop :=
  UnitaryVolumeMass.stABSprod D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch

def HerrExtensionClause (C' Cl Cg cb Cu cT CT C0 A C1 C δ : ℝ) : Prop :=
  UnitaryVolumeMass.stMIN D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ

def adm26 (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ : ℝ) : Prop :=
  UnitaryVolumeMass.stDEC D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

def AmplitudeBoundsConjunction (C' Cl Cg cb Cu cT CT C0 A C1 Cpr C C2 Ch δ : ℝ) : Prop :=
  adm22 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧ L2HilbertSchmidtPointwise D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  L2LossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ OperatorNormPointwiseBound D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C ∧
  AbsoluteConvergenceBesselIntegral D large₂ C' Cl Cg cb Cu cT CT C0 A C1 ∧ AbsoluteLossProductBound D large₂ C' Cl Cg cb Cu cT CT C0 A C C2 Ch ∧ HerrExtensionClause D large₂ C' Cl Cg cb Cu cT CT C0 A C1 C δ ∧
  adm26 D large₂ C' Cl Cg cb Cu cT CT C0 A C1 Cpr C Ch δ

end Amp

section HHb

variable (D : D7)

def HerrCocycleExtensionClass (large₂ : SizeData₂ D) (u u' : D.what₂.Word) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stHH D large₂ u u' C' Cl Cg cb Cu cT CT C0 A C

end HHb

section Comparison₂

def TermVolumeSmallCellBound (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (u u' : D.what₂.Word) (C1 : ℝ)
    (Y : LoopTie D large₂ X u u' C1) (C' Cl Cg cb Cu cT CT C0 A C : ℝ) : Prop :=
  UnitaryVolumeMass.stVol D large₂ X u u' C1 Y C' Cl Cg cb Cu cT CT C0 A C

end Comparison₂

section Family

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def admF6 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  ∀ δ > 0, OwnEv Fm fun C' Cl x i => adm6 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 δ

def admF7 (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => adm7 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def admF8 (Cg cb Cu cT CT C0 A : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => ∀ u u', adm8 (Fm.D x i) (Fm.L x i) u u' C' Cl Cg cb Cu cT CT C0 A

def FamilyRowsExist : Prop := ∀ x (i : Fm.Ix x), PlaneWaveLetters (Fm.D x i)

def FamilyWeylDimensionVandermondeQuotient (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => PlaneWaveIsometry (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyFourteenthHypothesis : Prop := ∀ x (i : Fm.Ix x) u u', adm14 (Fm.D x i) u u'

variable (C1 : ℝ) (X : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Y : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x) (u u' : (Fm.D x i).what₂.Word),
    LoopTie (Fm.D x i) (Fm.L x i) (X x hx i) u u' C1)

end Family

end Formalism.MainNotions.VanishingOnXAndXPlus

end
