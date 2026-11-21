import Mathlib
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal
import Formalism.SharpRestriction.Divisibility.ThetaNormsAndLinks
import Formalism.SharpRestriction.Divisibility.FamilyThetaDenominatorValues
import Formalism.SharpRestriction.Divisibility.BoundaryLocalData
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.IntegralModelsLocalData
import Formalism.SharpRestriction.Divisibility.WeightThresholdDefs
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.LogDiscriminantLeSquareSizeFamily
import Formalism.SharpRestriction.LevelLetterCocycles.CommutingEndomorphismPreservesInvariants
import Formalism.LocalRingCardinality.DataKap
import Formalism.SharpRestriction.Divisibility.ModuliIntegralCharts
import Formalism.LocalRingCardinality.DataParams
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.LocalToGlobal.NormalizedHeckeFactors.RingHomOfBaseOrderToFraction
import Formalism.SharpRestriction.Divisibility.WeightDegreeSizes
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.Divisibility.CanonicalTranslateJets
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.AbsolutelyIrreducibleSpan
import Formalism.SharpRestriction.Divisibility.AdmissibleRank.FreeFamilyOfLeavesAndAdmissible

noncomputable section

namespace Formalism.MainNotions.DIV

open Formalism.BasicNotions Formalism.MainNotions

section PDV08rec

variable (D : D7) (L : SizeData₂ D) {nch : NChoice D} (X : LiftErrorLocal.Loc D nch) (Z : ThetaNormsAndLinks.Loc8 X)

def ThetaNormLinkHypotheses (H : WeightAlgebra.KHyp) (C2 A2 CR CT CRd : ℝ) : Prop :=
  ThetaNormsAndLinks.admissible_unitary_of_inputs D X Z ∧ ThetaNormsAndLinks.SandwichExists D X ∧ ThetaNormsAndLinks.CharacterRankDiscriminant D X CRd ∧ ThetaNormsAndLinks.MirabolicIndexCond D ∧
    (ThetaNormsAndLinks.admR D nch ∧ ThetaNormsAndLinks.admG2 D ∧ ThetaNormsAndLinks.BadRowShareBound D L nch ∧ ThetaNormsAndLinks.EqualGoodMultiplicities D nch ∧ ThetaNormsAndLinks.SupLatticeGroupStable D) ∧ ThetaNormsAndLinks.SupSpansPsiPart D ∧
    (ThetaNormsAndLinks.AdditiveCharacterIntegrality D X ∧ ThetaNormsAndLinks.ScalingIntegrality D X ∧ ThetaNormsAndLinks.CrudeIntegrality D X ∧ ThetaNormsAndLinks.ThetaLevelPrimeIntegrality D X) ∧
    (ThetaNormsAndLinks.admT4 D X ∧ ThetaNormsAndLinks.NormDecompositionCond D X Z ∧ ThetaNormsAndLinks.ThetaKGroupStable D X Z ∧ ThetaNormsAndLinks.ThetaKEquivariantData D X Z ∧ ThetaNormsAndLinks.WeightGeneratorsInLattice D X) ∧
    (ThetaNormsAndLinks.RunColumnChoices D X ∧ ThetaNormsAndLinks.ScalarSizeConditions D L X H C2 A2 CR CT CRd ∧ ThetaNormsAndLinks.FurtherSizeConditions D L X H C2 A2 CR ∧ ThetaNormsAndLinks.GlobalScalarBounds D L X H ∧
      ThetaNormsAndLinks.RegularityOffTypePrimes D L X H)

end PDV08rec

section P18parts

variable {D : D7} {nch : NChoice D} (X : LiftErrorLocal.Loc D nch)

def UnitClauseAtBaseTuple : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (nch.twI w) j b (nch.k' w) ∅ 1 ≤ LiftErrorLocal.twistV0Submodule D nch w j b ∧
    (D.what₂.Ij D.what₂.muStar j (LiftErrorLocal.plS nch w b) : ℝ) ≤ (D.what₂.places.ramIdx (LiftErrorLocal.plS nch w b) : ℝ) * X.IsgBase w j b

def TwistedIndexBound (D : D7) : Prop := ∀ i0 w, LiftErrorLocal.Over D i0 w → ∀ j ∈ LiftErrorLocal.lifts D, TwistedAt D w →
  (D.what₂.jw (D.what₂.muTw w) j w : ℝ) ≤ (D.what₂.places.ramIdx w : ℝ) * (D.what₂.etaJ j w : ℝ)

end P18parts

structure Trip (D : D7) where
  B : WeightFamilies.Prov D
  P : ModuliIntegralCharts.Prov D
  W : WeightAlgebra.Prov D B P

section ChainF

variable {eps : ℝ} (Fm : FamP eps)

variable (XF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), LiftErrorLocal.Loc (Fm.D x i) (Fm.ex x hx i).nch)
  (ZF : ∀ x (hx : Fm.x1 < x) (i : Fm.Ix x), ThetaNormsAndLinks.Loc8 (XF x hx i))
  (YF : BoundaryLocalData.ProvF Fm (fun x hx i => (XF x hx i).P6))

structure LvG (Ob : WeightFamilies.ObjClass) (O8 : WeightAlgebra.ObjClass) (O18 : LiftErrorLocal.ObjClass) (K : WeightAlgebra.KAdm) (H : WeightAlgebra.KHyp)
    (C2h A2 CR CRd : ℝ) : Prop where
  ob : ∀ x hx i, Ob (Fm.L x i) (XF x hx i).B
  o8 : ∀ x hx i, O8 (Fm.L x i) (XF x hx i).B (XF x hx i).P6 (XF x hx i).W
  o18 : ∀ x hx i, O18 (Fm.L x i) (Fm.ex x hx i).nch (XF x hx i)
  a14 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      WeightAlgebra.adm2 (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CG K.AG ∧
      WeightAlgebra.adm3 (Fm.L x i) (XF x hx i).W H.CA K.Cf K.Af ∧
      WeightAlgebra.ArchimedeanSignatureMatching (Fm.L x i) (XF x hx i).W H.CA H.C1 H.A1 K.CW K.AW
  b1 : WeightFamilies.familyUnitInput Fm (fun x hx i => (XF x hx i).B)
  b3 : WeightFamilies.FamilyAdmittedLemmaThree Fm (fun x hx i => (XF x hx i).B)
  bB : WeightFamilies.TransferenceTheoremCond
  bC : WeightFamilies.ChowlaSelbergFamily Fm
  a66 : BoundaryLocalData.AdmFx Fm (fun x hx i => (XF x hx i).P6) YF
  lv : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      ThetaNormLinkHypotheses (Fm.D x i) (Fm.L x i) (XF x hx i) (ZF x hx i) H C2h A2 CR (Fm.Ct + 1) CRd
  a79 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x,
      UnitClauseAtBaseTuple (XF x hx i) ∧ TwistedIndexBound (Fm.D x i) ∧ LiftErrorLocal.adm9 (Fm.D x i) (XF x hx i)
  aU : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, ∀ w, TwistedAt (Fm.D x i) w → PDVN.UAt (XF x hx i) w
  aTG : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, TwGoodAt (Fm.D x i) (Fm.ex x hx i).nch (XF x hx i).I
  a12 : ∃ x0 : ℝ, ∀ x (hx : Fm.x1 < x), x0 ≤ x → ∀ i : Fm.Ix x, N.LocsCoverTw (Fm.D x i)

end ChainF

end Formalism.MainNotions.DIV

end
