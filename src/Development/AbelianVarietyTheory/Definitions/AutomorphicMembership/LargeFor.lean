import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PeriodComparisonProvisional
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingKrullDimIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsTangent
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LinearIndependentOfCutSec
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MSmoothOfWeightIffIsCInf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClosedPointGeometricFibresFinite
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValAtAlgebraMap
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumLogEmbeddingAddFinsumLogAdicAbvEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.RingKrullDimRingOfIntegers
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LocStOfLoc
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.GeoTiedPGraft
import Formalism.LocalToGlobal.LatticeGeometry.ViewsC
import Formalism.SharpRestriction.Divisibility.PrinLevClass
import Formalism.SharpRestriction.Divisibility.LatticeTransfer
import Formalism.SharpRestriction.Divisibility.PlaceRankTwoOne
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.SharpRestriction.Divisibility.PrimeDegreeVariant
import Formalism.SharpRestriction.Divisibility.ZetaProductPairs
import Formalism.SharpRestriction.Divisibility.InnerProductFormulaField
import Formalism.SharpRestriction.Divisibility.KudlaSiegelWeil
import Formalism.SharpRestriction.Divisibility.LocalQuadraticParts
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.SubsingletonRankIndicatorIff
import Formalism.SharpRestriction.Divisibility.WeightAlgebra
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.WeightFamilies
import Formalism.SharpRestriction.Divisibility.LocalNonemptiness.LiftErrorLocal
import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.ExampleSatisfiesConditionsAtFive
import Formalism.LocalRingCardinality.DataExtra
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalShimX
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SubRkOfPsiOfEqRkOfCEmb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsProvisionalDivX
import Formalism.LocalToGlobal.LatticeGeometry.GeoTiedP

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.Geo GlobalTheory.TrueGeo GlobalTheory.LocM GlobalTheory.ShFam.Pad

namespace GlobalTheory.ShFam

abbrev JC (D : D7) : Type := ∀ (p : ℕ) [Fact p.Prime], PlL D p → (DV.KW p →+* ℂ)

def JC.Pinned {D : D7} (jC : JC D) : Prop := ∀ (p : ℕ) [Fact p.Prime] (la : PlL D p), JcPin D p la (jC p la)

abbrev KitT {D : D7} {A : Amb D} {N j : ℕ} {S : Sig A N j} {κ : Lv A} (s : FinalTheorems S κ) (L : CmList A) (jC : JC D) : Type 1 :=
  Kit s L (cxSt D.what₂.LL) jC ngTrue

abbrev KitClass (D : D7) : Type 1 :=
  ∀ (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ) (L : CmList A) (jC : JC D),
    KitT s L jC → (s.Comp → D.what₂.Tau → ℝ) → Prop

variable {D : D7}

structure FamOver (Q : KitClass D) (T : Top D) (h : LawsP T) (c : ℕ) : Type 1 where
  F : SrcFam (ambOf T.Q h.pins.1)
  t : ParTie T.Q h.pins.1 F
  exp : F.κs.l.A = 15 ^ c
  L : CmList (ambOf T.Q h.pins.1)
  jC : JC D
  pin : jC.Pinned
  k : Kits F L (cxSt D.what₂.LL) jC ngTrue
  d : ∀ N j hN hj κ, (F.src N j hN hj κ).Comp → D.what₂.Tau → ℝ
  mem : ∀ N j hN hj κ, Q _ N j _ κ (F.src N j hN hj κ) L jC (k N j hN hj κ) (d N j hN hj κ)
  hg : F.κg.primes = Finset.univ.image D.host.g
  P : FormsOver (cutSt _) (resSt _) k
  forms : FormsAre h t (cutSt _) (resSt _) k P
  prov : ∃ (I : Type) (dat : I → Dat D (Lv (ambOf T.Q h.pins.1))) (hI : ∀ i, (dat i).Indef) (iW : ℕ → I),
    (∀ w : Dat D (Lv (ambOf T.Q h.pins.1)), w.Indef → ∃ i, (dat i).N = w.N ∧ (dat i).j = w.j ∧ (dat i).κ = w.κ) ∧
    (∀ j, 1 ≤ j → j < D.R.m → dat (iW j) = datW D F.κg j) ∧
    T.G.P = indefiniteDataFamily (shimOf (cutSt _) (resSt _) k) I dat hI ∧ ∀ j, 1 ≤ j → j < D.R.m → HEq (T.G.dat j) (iW j)

namespace FamOver

end FamOver

end GlobalTheory.ShFam
