import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPullbackPow
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.SameUnifRefl
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatIsoUnitGenerator
import Development.AbelianVarietyTheory.BlockTheory.CMModuli.FlatTorsionIsomorphism
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsSmulPtSmulPt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.FormallyUnramifiedMulInvertibleInteger
import Development.AbelianVarietyTheory.Counterexamples.JetSurvey.ExistsUniquePairIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionDescentFiniteEtaleCover
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsUniversalTorsionPairPolAV
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsAdicColimitOfIsFiniteNoetherian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.FinitePartImageGeneric
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.GenericPartImagePullback
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.TorsionFiniteFlatIff
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.IsFiniteAndFlatMulAbelianScheme
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPtsEquiv
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.LinearUniformisationTorsionIsomorphism

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.FlatTors.TorsMapExists

open ReciprocityTheory.ChartRestriction.G.DVR

theorem isPull_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' T'' : Over (Sp R)}
    {a : T'.left ⟶ T.left} {b : T''.left ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPt D T''}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPull b g' g'') : GtPt.IsPull (b ≫ a) g g'' := by
  refine ⟨by rw [h'.1, h.1, Category.assoc], fun χ => corr_of_val D.P.isLB fun y J hJ => ?_⟩
  rw [val_corr hJ (h'.2 χ), val_pull hJ, val_corr hJ (h.2 χ), val_pull hJ, val_pull hJ, Category.assoc]

theorem isPullF_trans {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {T T' : Over (Sp R)}
    {F : Type} [Field F] [Algebra (FractionRing R) F]
    {a : T'.left ⟶ T.left} {b : Sp F ⟶ T'.left} {g : GtPt D T} {g' : GtPt D T'} {g'' : GtPtF D F}
    (h : GtPt.IsPull a g g') (h' : GtPt.IsPullF F b g' g'') : GtPt.IsPullF F (b ≫ a) g g'' :=
  isPull_trans (T'' := TF (R := R) F) (g'' := ⟨g''.b, g''.s, g''.isGen, g''.s_zero, g''.mult⟩) h h'

end GlobalTheory.FlatTors.TorsMapExists
