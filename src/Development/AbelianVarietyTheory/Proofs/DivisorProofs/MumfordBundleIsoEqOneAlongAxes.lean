import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExtId
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnimodMod
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialFirstAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoNormalisedRespectsLaws
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsMumfordBundleIsoValueOneOriginPolarised
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoValueOneZeroFirstFactor
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RefinesPolarisedDataBaseChangeSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoCartesianSquareTrivialSecondAxis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoOriginOneOfGenericOriginDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MumfordBundleIsoGenericOriginOneTautologicalBase
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg GlobalTheory.TChart GlobalTheory.UT GlobalTheory.Mum.Two
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.TInj

noncomputable section

namespace GlobalTheory.TInj

theorem lamVal_axes_one : ∀ {o W : Type} [CommRing o] [CommRing W] [IsLocalRing W] (T : TautBase o W) {I : Type} [Fintype I] (ε : I → LinearMap.BilinForm ℤ (Fin T.r → ℤ)) (n : ℕ) (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (ω : W →+* V) (s : I → V) (e : D.X ≃+ (Fin T.r → ℤ)) (β : D.P.A.left ⟶ T.B.left) (ββ : (G2 D.P.A).left ⟶ (G2 T.B).left) (w : LB.Iso (abelian₂ D.P.A D.P.L) ((abelian₂ T.B T.M.L).pull ββ)), D.TauBimult → From T ω s ε n D e β ββ w → ∀ (Z : Over (Sp V)) (y : Z ⟶ D.P.A) (z : Z.left) J J', Good T.M.L z J → Good D.P.L z J' → lamVal w (lift (1 : Z ⟶ D.P.A) y).left z J J' = 1 ∧ lamVal w (lift y (1 : Z ⟶ D.P.A)).left z J J' = 1 := by
  intro o W _ _ _ T I _ ε n V _ _ D ω s e β ββ w hB hF Z y z J J' hJ hJ'
  letI := D.P.isAb.comm
  have hpb := hF.1
  have hsq := hF.2.1
  have hw := hF.2.2.1
  have N := _root_.GlobalTheory.GenOrigin.lamVal_origin_of_generic T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB (spMap ω) β ββ w hpb hsq hw
    (_root_.GlobalTheory.TInj.lamVal_origin_of_from T ε n V D ω s e β ββ w hB hF)
  exact ⟨_root_.GlobalTheory.MumRigidZeroPull.lamVal_one_left_pull T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ',
    _root_.GlobalTheory.MumRigidZero.lamVal_one_right_base T.B D.P.A T.M.L D.P.L T.M.isLB D.P.isLB D.P.isAb (spMap ω) β ββ w hpb hsq hw N Z y z J J' hJ hJ'⟩

end GlobalTheory.TInj
