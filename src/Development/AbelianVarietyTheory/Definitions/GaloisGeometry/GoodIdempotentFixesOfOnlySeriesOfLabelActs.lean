import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ExistsUniqueVec
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsInertiaCharpolyFactorOfTameType
import Formalism.SharpRestriction.LevelLetterCocycles.IsobaricMultiplicityOne
import Formalism.SharpRestriction.LevelLetterCocycles.PlaceLabelTeichmuller
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.InjPrimeTo
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.LocalGlobalAboveL
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.RegularAlgebraicPurity
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HeckeLAdicParameterAbove
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweDualityGL
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.BernsteinUnitaryProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.ChebotarevDegreeOneIffCheb
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable

noncomputable section

namespace GlobalTheory.NRows

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N GlobalTheory.RowCopy

structure Hypotheses₂ : Prop where
  bz : GlobalTheory.Published.BernsteinZelevinskyFiniteness
  bern : GlobalTheory.Published.BernsteinUnitaryProductIrreducible
  geo : GlobalTheory.Published.GeometricLemma
  unl : GlobalTheory.Published.UnlinkedProductIrreducible
  mp : GlobalTheory.Published.DepthZeroJacquetInjective
  howe : GlobalTheory.Published.HoweDualityGL
  js : GlobalTheory.Published.JacquetShalika
  fin : GlobalTheory.Published.AutomorphicFormsFiniteGL
  temp : GlobalTheory.Published.CohomologicalCsdTempered
  gal : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal
  car : GlobalTheory.Published.LocalGlobalAboveL
  clo : GlobalTheory.Published.RegularAlgebraicPurity
  art : GlobalTheory.Published.GlobalArtinReciprocity
  chA : GlobalTheory.Published.HeckeLAdicCharacterAbove
  chP : GlobalTheory.Published.HeckeLAdicParameterAbove
  berger : GlobalTheory.Published.DeRhamPotSemistable
  cheb : GlobalTheory.Published.ChebotarevDegreeOne

structure RowsA (D : D7) : Prop where
  tieLab : SumRepresentations.tieLab D
  hecke : HeckeSplitOne D
  tie0 : SumRepresentations.tie0 D
  a2 : SumRepresentations.adm2 D
  an1 : T2.SumRepresentations.StrongMultiplicityOneCuspidalSums D.nd D.naut
  an2 : T2.SumRepresentations.IsobaricMultiplicityOne D.nd D.naut
  a5 : SumRepresentations.adm5 D
  temp : SumRepresentations.adm7 D
  g4p : SumRepresentations.CuspidalGaloisUnramified D
  gsp : ∀ (k : Fin 2) (v : D.nd.PlG k), IsSplitPl D.host (D.naut.plGw k v)

structure RowsB (D : D7) : Prop where
  rowSize : RowSize D
  a3 : SumRepresentations.adm3 D
  a4 : SumRepresentations.ArchimedeanSignatureMatching D
  thetaOne : ThetaOne D

structure RowsC (D : D7) : Prop where
  c4b : JointOccurrenceCondition D
  rho : GlobalDatumResidualRepCondition D
  dz : GlobalDatumDepthZeroCondition D
  parUp : ∀ i, ParUpRec D.nd D.naut i
  downMem : ∀ i, DownMemRec D.nd D.naut i
  goodPart : ∀ i, GoodPartRec D.nd D.naut i

def LamUsed (D : D7) : Prop :=
  ∀ μ, (μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) → ∀ j : Fin D.R.m, LamPos D μ (j.1 + 1)

def GoodIdempotentFixesLocalisationForms (D : D7) : Prop :=
  ∀ (i : D.nd.Loc) (σ' : D.ntypes.Par), ∀ F ∈ D.ntypes.MtPar (D.nd.mu i) (D.nd.j i) σ',
    D.ntypes.goodPar σ' → D.ntypes.onMt (D.nd.mu i) (D.nd.j i) D.ntypes.e0 F = F

def GoodIdempotentReadsAsGoodTypeProjector {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} {tp : Formalism.L2.Host.TupTied D cf nch}
    (X : GlobalTheory.NJoin.RealAt D cf nch tp) : Prop :=
  ∀ μ (hμ : Formalism.IndefR.RecTie.Used0 D μ) (j : Fin D.R.m) (f : D.what₂.Mt μ (j.1 + 1)) y,
    X.R.extV j (X.tupT μ) y = X.fn hμ j f →
      (D.ntypes.onMt μ (j.1 + 1) D.ntypes.e0 f = f ↔ GlobalTheory.DownLift.GoodVt X.R j (X.tupT μ) y)

structure Tied (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 where
  P : GlobalTheory.NPin.Pin hL D
  X : GlobalTheory.NJoin.RealAt D P.cf P.C P.tp
  agree : GlobalTheory.NJoin.Agree X P.M P.rep
  e0read : GoodIdempotentReadsAsGoodTypeProjector X

structure Named {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (T : Tied hL D) : Prop where
  hypO : SumRepresentations.hypO D
  c1 : GlobalDatumCompatibility D
  bc : SphericalInertData.Conclusion1 D
  lam : LamUsed D
  isot : SumRepresentations.adm8 D
  ser : GlobalTheory.TypeLeaf.SerLoc D
  typeNZ : ∀ j t, GlobalTheory.DownLift.TypeNZ T.X.R j t

structure Inputs (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) : Type 1 extends toRowSideFamily : Tied hL D where
  named : Named toRowSideFamily

structure Rows (D : D7) : Prop where
  a : RowsA D
  b : RowsB D
  c : RowsC D
  typeNZ : ∀ i, TypeNZRec D.nd D.naut i
  rank : ∀ L : SizeData₂ D, TwistedPlaces.adm3 L

theorem LamUsed.at {D : D7} (h : LamUsed D) {μ} (hμ : μ = D.what₂.mu0 ∨ ∃ w, μ = D.what₂.muAt w) {j : ℕ}
    (h1 : 1 ≤ j) (h2 : j ≤ D.R.m) : LamPos D μ j := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 1 := ⟨j - 1, by omega⟩
  exact h μ hμ ⟨k, by omega⟩

theorem LamUsed.loc {D : D7} (h : LamUsed D) (i : D.nd.Loc) : LamPos D (D.nd.mu i) (D.nd.j i) :=
  h.at (Or.inr ⟨D.nd.w i, (D.nd.mu_w i).trans ((D.what₂.muAt_or _).resolve_left (D.nd.w_tw i)).symm⟩)
    (D.nd.j_range i).1 (D.nd.j_range i).2

theorem goodIdempotentFixes_of_onlySeriesOfLabelActs {D : D7} (h : GlobalTheory.TypeLeaf.SerLoc D) : GoodIdempotentFixesLocalisationForms D := fun i σ' F hF hg =>
  (PlaceLabelTeichmuller.idempotent_action_on_forms D (D.ntypes.cenMt (D.nd.mu i) (D.nd.j i)) σ' F fun k v f hf => h i σ' k v f F hF hf).1 hg

namespace Inputs

variable {hL : GlobalTheory.Published.LocalLanglandsGL} {D : D7} (I : Inputs hL D)
include I

theorem lam : LamUsed D := I.named.lam

theorem isot : SumRepresentations.adm8 D := I.named.isot

end Inputs

end GlobalTheory.NRows

end
