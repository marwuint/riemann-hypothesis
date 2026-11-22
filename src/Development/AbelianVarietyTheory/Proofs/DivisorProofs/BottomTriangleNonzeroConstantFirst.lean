import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFinPt
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.IntegralFundamentalDomainEqSumDoubleCoset
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteBottomTowerConstantsDifferByFactor
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ClassSumIntegral
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MeasurePreservingMulRightOfMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomTriangleLevelFixesVector
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomPairModularTwistIdentity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.Theta IsDedekindDomain NumberField Finset MeasureTheory
open Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 Formalism.L2.Indef.Tree.ArchimedeanLeafBounds.Cuts
open Formalism.DivisionValues (vw)
open GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.FunObj.SqNum GlobalTheory.RowTest
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
open GlobalTheory.NormSum (Pair Tup)
open Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.BotClassSumSmall

open scoped ComplexOrder

open GlobalTheory.DefiniteClassAvg in

theorem openCompact {D : D7} {T : Type} {A A' WW : HSp D} (X : Tri T A A' WW) (hstd : X.rA'.IsStd) :
    IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) ∧
    IsCompact (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
  have hJo : IsOpen (((Formalism.L2.DIV.St X.rA'.β).comap (Lev.finE A') : Subgroup (GA D A')) : Set (GA D A')) := by
    refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
    filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ A' X.rA'.β ∅] with κ h1
    exact h1.2.1
  have hV : ∀ φ : D.host.E →+* ℂ, (A'.gram.map φ).PosDef := fun φ => by
    rw [hstd.1, Matrix.map_one φ (map_zero φ) (map_one φ)]
    exact Matrix.PosDef.one
  let V' : HSp D := { A' with sig := fun _ => (A'.rank, 0) }
  have hS' : V'.SigOK := fun τ => GlobalTheory.Proof.GenusMassSignature.hasSignature_of_posDef (hV τ)
  have hD' : V'.IsDefinite := fun τ => Or.inl rfl
  have hGc : IsCompact (GinfC A' : Set (GA D A')) := Formalism.IndefR.Eqv.isCompact_GinfC (V := V') hS' hD'
  have hLc : IsCompact ((Lev.levA A' (Formalism.L2.DIV.St X.rA'.β) : Subgroup (GA D A')) : Set (GA D A')) := by
    obtain ⟨C, hC, hCm⟩ := GlobalTheory.ParahoricCompact.exists_compact A' X.rA'.β
    refine hC.of_isClosed_subset ((GlobalTheory.Ker.CongTop.isClosed_GfC A').inter
      (Subgroup.isClosed_of_isOpen _ hJo)) fun k hk => ?_
    obtain ⟨hk1, hk2⟩ := Lev.mem_levA.1 hk
    exact hCm k hk1 hk2
  refine ⟨hJo, (hLc.mul hGc).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ hJo) ?_⟩
  intro k hk
  exact ⟨finPart A' k, finPart_mem_levA A' hk, realPart A' k, realPart_mem A' k, finPart_mul_realPart A' k⟩

end GlobalTheory.BotClassSumSmall
