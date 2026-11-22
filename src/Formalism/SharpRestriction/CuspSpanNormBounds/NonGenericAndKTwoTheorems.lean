import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.CuspSpanNormBounds.LeSCSCl
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.SharpRestriction.CuspSpanNormBounds.StandingNumericalData
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Formalism.SharpRestriction.CuspSpanNormBounds.FlagEEqHyperbolic
import Formalism.SharpRestriction.CuspSpanNormBounds.NormalizedLocalScale
import Formalism.SharpRestriction.CuspSpanNormBounds.CntPartners
import Formalism.HermitianLattices.StatementMass

noncomputable section

open ValuativeRel NumberField MeasureTheory
open scoped ENNReal

namespace Formalism.MainNotions.NonGenericAndKTwoTheorems

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.Cnt Module

attribute [local instance] Formalism.BasicNotions.Host.cmStar

def NonGenericLocalBound (k r : ℕ) (C : ℝ) : Prop :=
  ∀ (F : Type) [Field F] [ValuativeRel F] [TopologicalSpace F]
    (E : Type) [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
    (M : Loc.Model F E), M.OK →
    ∀ (V : Type) [AddCommGroup V] [Module E V] (H : Loc.HermSp M V),
      Module.finrank E V = k + 2 * r + 1 →
      ∀ P : LocNG.FPair H r, P.RelG (LocNG.theta M) → LocNG.NGAt k P C

def Conclusion1 (D : D7) (C : ℝ) : Prop := 4 * D.R.rS + 7 ≤ D.R.k → NonGenericLocalBound D.R.k D.R.rS C

section Hyps

variable (D : D7) (large₂ : SizeData₂ D)

def KTwoParameterConditions (Cl Cg CT : ℝ) : Prop :=
  Cl * (D.R.m : ℝ) ^ 6 * large₂.sc.L ≤ (D.R.k : ℝ) * Real.log D.R.k ∧
  (∀ i : Fin 2, ((D.R.k : ℝ) * large₂.sc.b) ^ 8 ≤ (D.host.g i : ℝ) ∧ (D.host.g i : ℝ) ≤ large₂.sc.b ^ Cg) ∧
  (∀ (τ : D.what₂.Tau) (a c : Fin D.R.r), a ≠ c →
    Cl * (D.R.k : ℝ) * (D.R.m : ℝ) ^ 3 < |lamS D.R (D.hc τ) a - lamS D.R (D.hc τ) c|) ∧
  Cl * Real.log D.host.rdE ≤ large₂.sc.L ∧
  Real.log (D.R.f : ℝ) ≤ (D.R.rS : ℝ) ^ 2 ∧
  (∀ u : D.what₂.Word, ((D.mem u).A.T : ℝ) ≤ large₂.sc.b ^ (CT * (D.R.m : ℝ)) ∧
    Nat.Coprime (D.mem u).A.T (D.host.g 0 * D.host.g 1)) ∧
  Formalism.HermitianLatticesTheory.IsCMUnram D.host.E

def KTwoHypotheses (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  Hyp0 D large₂ C' Cl Cg cb Cu cT CT C0 ∧ KTwoParameterConditions D large₂ Cl Cg CT

def TermsPP (u u' : D.what₂.Word) : Set (D.s.Term u u') := {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Kpp (u u' : D.what₂.Word) : D.s.Cu u' →L[ℂ] D.s.Cu u := KOf D.s u u' {t | D.s.Gterm t = 0 ∧ ¬ D.s.isId t}

def Conclusion2 (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u : D.what₂.Word,
    Summable (fun t : TermsPP D u u => D.s.aTerm u u t.1) ∧
    hsNormSq (Kpp D u u) ≤ (D.duS u : ℝ) * Real.exp (-((D.R.k : ℝ) * D.R.f * Real.log D.R.k))

def PointsLemma (C' Cl Cg cb Cu cT CT C0 : ℝ) : Prop :=
  KTwoHypotheses D large₂ C' Cl Cg cb Cu cT CT C0 → ∀ u u' : D.what₂.Word, u ≠ u' →
    ∀ t : D.s.Term u u', D.s.Gterm t = 0 → D.s.aTerm u u' t = 0

end Hyps

def adm7 : Prop :=
  ∀ (k : ℕ) (u u' : Fin k → ℝ) (H H' : Type)
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
    (π : Matrix (Fin k) (Fin k) ℂ → (H →L[ℂ] H)) (ρ : Matrix (Fin k) (Fin k) ℂ → (H' →L[ℂ] H')),
    IsHCTypeU k u π → IsHCTypeU k u' ρ → u ≠ u' →
    ∀ P : H' →L[ℂ] H, (∀ h ∈ UJset (allPos k), P.comp (ρ h) = (π h).comp P) → P = 0

section Packet

variable (D : D7) (large₂ : SizeData₂ D) (X : TermTie D) (Gv : GaugeVol D)

def NonGenericLocalBoundOfLargeRank (CN : ℝ) : Prop := Conclusion1 D CN

end Packet

section Family

variable {eps : ℝ} (Fm : FamP eps) (At : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, TermTie (Fm.D x i))
  (Gv : ∀ x, Fm.x1 < x → ∀ i : Fm.Ix x, GaugeVol (Fm.D x i))

def Conclusion1Family (CN : ℝ) : Prop := ∀ x (i : Fm.Ix x), Conclusion1 (Fm.D x i) CN

def Conclusion2Family : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => Conclusion2 (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def Conclusion3Family : Prop := ∀ Cg cb Cu cT CT C0 : ℝ,
  OwnEv Fm fun C' Cl x i => PointsLemma (Fm.D x i) (Fm.L x i) C' Cl Cg cb Cu cT CT C0

def FamilyNonGenericLocalBound (CN : ℝ) : Prop := Conclusion1Family Fm CN

end Family

end Formalism.MainNotions.NonGenericAndKTwoTheorems

end
