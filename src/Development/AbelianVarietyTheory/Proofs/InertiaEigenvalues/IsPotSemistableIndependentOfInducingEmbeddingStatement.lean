import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotSemistableIndependentOfInducingEmbedding
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeightRegularOfExt
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RankOneUnitary
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ContinuousIotaOQOfData
import Formalism.SharpRestriction.LevelLetterCocycles.DataN
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalGaloisRepDecompositionInduced
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfWdMkPhiDPow
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinrankLetterHomComp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.KummerNotFrac
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficieStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankDpstUnramifiedLeDimRepresentation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DpstRankLeDimension

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isPotSemistable_independent_of_inducingEmbedding : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) → ∀ (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (A : ValuationSubring Ω) (O O' : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] [CommRing O'] [Algebra ℤ_[l] O'] [TopologicalSpace O'] (Bw : LocBridge l E Ω (Dec (F := E) A) O) (Bw' : LocBridge l E Ω (Dec (F := E) A) O'), GlobalTheory.Pst.Induces Bw → GlobalTheory.Pst.Induces Bw' → ∀ (a : ℕ) (r : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)), Continuous (fun g => ((r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l))) → GlobalTheory.Pst.IsPstAt P Bw r → GlobalTheory.Pst.IsPstAt P Bw' r := by
  first | exact @GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | exact GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge | (intros; apply GlobalTheory.Pst.PstBridge.isPstAt_indep_bridge <;> assumption)
