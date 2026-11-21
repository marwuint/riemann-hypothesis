import Formalism.SharpRestriction.LevelLetterCocycles.SplitROfSteps
import Formalism.SharpRestriction.LevelLetterCocycles.FontExAll

noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

def GenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → genR D

def LiftStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → liftR D

def NormStep : Prop := ∀ D : D7, normR D

def DvdStep : Prop := dvdR

def QuotStep : Prop := ∀ D : D7, adm8 D → adm11 D → quotR D

def DeltaInvariantUniformizer : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F),
    adm1 D HW F Cm → p9R D HW

def ExtStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → extOfR D HW

def WStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → wKillR D HW

def KerLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → FontExAll D HW F → kerLamR D HW

def NinLamStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → ninLamR D HW

def GradNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gradNR D HW

def FrobPiNStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → frobPiNR D HW

def GamPiStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → gamPiR D HW

def OneGenStep : Prop :=
  ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F)
    (CA CB CK : ℝ), Adm1 D HW F Cm CA CB CK → oneGenR D HW

end Formalism.MainNotions.N.Ln34

end
