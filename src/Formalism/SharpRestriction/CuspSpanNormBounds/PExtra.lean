import Formalism.SharpRestriction.CuspSpanNormBounds.RadialChainStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.HereditaryPositivity
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalBesselAndTopKernel
import Formalism.SharpRestriction.CuspSpanNormBounds.NonGenericAndKTwoTheorems
import Formalism.SharpRestriction.CuspSpanNormBounds.LatticeIndexAndWeightTheory
import Formalism.SharpRestriction.CuspSpanNormBounds.UniformConstantsAndStatements
import Formalism.SharpRestriction.CuspSpanNormBounds.OnePlaceEstimates
import Formalism.SharpRestriction.CuspSpanNormBounds.CayleySignature
import Formalism.SharpRestriction.CuspSpanNormBounds.FrobeniusProjectedBounds
import Formalism.SharpRestriction.CuspSpanNormBounds.AdmissibleBoundsFromSource
import Formalism.SharpRestriction.CuspSpanNormBounds.CongruenceAtSplitFrobeniusHolds
import Formalism.SharpRestriction.CuspSpanNormBounds.SBridge
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl

noncomputable section

namespace Formalism.MainNotions.PX

section GroupS0

open Formalism.BasicNotions Formalism.MainNotions.S NumberField IsDedekindDomain

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def Exp (D : D7) : Prop := ∀ u u' : D.what₂.Word, KExpansion D.s u u' ∧ KAbsConv D.s u u'

def V0 (D : D7) : Prop := ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), ¬ D.s.relevant t → D.s.aTerm u u' t = 0

def GDr (D : D7) (X : TermTie D) : Prop :=
  ∀ (u u' : D.what₂.Word) (t : D.s.Term u u'), D.s.Gterm t ≠ 0 →
    Dl (X.fl t).fl (X.fl' t).fl (D.R.rS + 1) ≠ 0 ∧
    (Dl (X.fl t).fl (X.fl' t).fl D.R.rS ≠ 0 → ∀ τ, 0 < (embS D τ (Lat.Gval (X.fl t) (X.fl' t))).re)

section Family

variable {eps : ℝ} (Fm : FamP eps)

def RanksF (C0 Cg cb Cu cT CT : ℝ) : Prop := LocalBesselAndTopKernel.FamilyRanksHypothesis Fm C0 Cg cb Cu cT CT

end Family

end GroupS0

section GroupS1

open Formalism.MainNotions.S

def lemmaB (CB : ℝ) : Prop := TopsChoicePartA.LemmaB CB

def t22 : Prop := UnitaryLevelOperators.DiagonalEntryIdentity

def LetterIdentitiesRTT : Prop := UnitaryLevelOperators.stLetters

def dualList (C Co Cd : ℝ) : Prop := UnitaryLevelOperators.stDualList C Co Cd

def PointwiseIntegrationByParts : Prop := UnitaryLevelOperators.stIBP

def ConjugationIdentity : Prop := UnitaryLevelOperators.stThLog

def PlaneWaveLetterIdentities : Prop := UnitaryLevelOperators.stWaveLetters

def slices (Cs : ℝ) : Prop := UnitaryLevelOperators.stSlices Cs

def slicesOrb (Cs : ℝ) : Prop := GramWordSpace.Slices Cs

def lettersExist : Prop := GramWordSpace.LettersExist

def smooth (CB : ℝ) : Prop := UnitaryLevelOperators.stSmooth CB

def germ (C₁ C₂ : ℝ) : Prop := UnitaryLevelOperators.stGerm C₁ C₂

structure S1 (CB Co Cd Cs Cg₁ Cg₂ : ℝ) : Prop where
  lemmaB : lemmaB CB
  t22 : t22
  LetterIdentitiesRTT : LetterIdentitiesRTT
  dualList : dualList CB Co Cd
  PointwiseIntegrationByParts : PointwiseIntegrationByParts
  ConjugationIdentity : ConjugationIdentity
  PlaneWaveLetterIdentities : PlaneWaveLetterIdentities
  slices : slices Cs
  slicesOrb : slicesOrb Cs
  smooth : smooth CB
  lettersExist : lettersExist
  germ : germ Cg₁ Cg₂

end GroupS1

section GroupS5

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.UnitaryVolumeMass Formalism.MainNotions.S.Bridge

variable {eps : ℝ} (Fm : Formalism.MainNotions.FamP eps)

def StdHypS (Cg cb Cu cT CT C0 Ch Cβ : ℝ) : Prop :=
  ∀ Cs Cs', OwnEv Fm fun C' Cl x i => StdOfHyp (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 Ch Cs Cs' Cβ

def TFrame (Cg cb Cu cT CT C0 : ℝ) : Prop :=
  OwnEv Fm fun C' Cl x i => Cnt.Hyp0 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0 →
    ∀ w, 1 ≤ Tr (Fm.D x i) w * kaS (Fm.D x i) ^ (2 * (Fm.D x i).R.rS)

end GroupS5

end Formalism.MainNotions.PX

end
