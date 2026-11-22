import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ValCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExpandsGSum
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.FrameNStHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ConstantCoeffDmonNCongr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.GroupExpansionBijectiveOfCompleteDVR
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalJetsPowerProduct
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.PsiWeightZeroProduct
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.StalkMapInjectiveOfFlat

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open ReciprocityTheory.ChartRestriction.G.DVR ReciprocityTheory.ChartRestriction.G.DVR.QForm Formalism.MainNotions.ModuliIntegralCharts.H1 Formalism.MainNotions.ModuliIntegralCharts.H1.ExpBijectiveUniformisation Formalism.MainNotions.ModuliIntegralCharts.H1.GSt
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ
attribute [local instance] Over.cartesianMonoidalCategory
open Formalism.MainNotions.ModuliIntegralCharts.H1.BoxTuple Formalism.MainNotions.ModuliIntegralCharts.H1.BidegreeTwoJet GlobalTheory GlobalTheory.PowGerm
open ReciprocityTheory.ChartRestriction.G.TB (colM dAct)

namespace GlobalTheory.PairingLinear

def linOfComb {F M N : Type} [Field F] [AddCommGroup M] [Module F M] [AddCommGroup N] [Module F N] (f : M → N)
    (h : ∀ (l : ℕ) (c : Fin l → F) (s : Fin l → M), f (∑ i, c i • s i) = ∑ i, c i • f (s i)) : M →ₗ[F] N where
  toFun := f
  map_add' a b := by simpa using h 2 ![1, 1] ![a, b]
  map_smul' c a := by simpa using h 1 ![c] ![a]

theorem exists_germ_linearMap (hL : Laws) (hL2 : Laws2) (hL4 : Laws4) (hT : TwistBaseChangeStatement)
    (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] [IsAdicComplete (maximalIdeal V) V]
    (D : DegData V (maximalIdeal V)) (A : PolAV (Spec (CommRingCat.of (FractionRing V)))) (G : Over (Sp V))
    [GrpObj G] [IsCommMonObj G] (U : Unif (maximalIdeal V) D A G) (κ : Type) [Fintype κ] [DecidableEq κ]
    (z : JetPts G κ) (hz : IsUnivJ G κ z) (τ : Frames U.LG.L z) (hτ : τ.Gen) (hτT : τ.Trunc)
    (F : Type) [Field F] [Algebra (FractionRing V) F] [Algebra V F] [IsScalarTower V (FractionRing V) F]
    (q : ℕ) (hq : 1 ≤ q) :
    ∃ gm : Fam D.toPre F q →ₗ[F] MvPowerSeries κ F,
      (∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = gm t) ∧
      ∀ t, ∃ σ', U.ExpandsG F q σ' t ∧ GermA U.toUnifPre z τ F q σ' (gm t) := by
  obtain ⟨huniq, hlin, hex⟩ := GlobalTheory.GermBasic.main V D A G U κ z hz τ hτ F q
  have hbij := (GlobalTheory.expandsG_bijective_of_dvr hL hL2 hL4 hT V D A G U F q hq).2
  choose S hS hSu using hbij
  choose Γg hΓ using hex hτT
  have key : ∀ t σ' h, U.ExpandsG F q σ' t → GermA U.toUnifPre z τ F q σ' h → h = Γg (S t) := by
    intro t σ' h he hg
    obtain rfl := hSu t σ' he
    exact huniq _ _ _ hg (hΓ _)
  refine ⟨linOfComb (fun t => Γg (S t)) fun l c s => ?_, key, fun t => ⟨S t, hS t, hΓ _⟩⟩
  let σ' : U.SecGF F q := GlobalTheory.ExpansionLinear.secComb
    (fun i => scal (fst (TFK (R := V) F) ((Over.pullback (jK V)).obj G)).left (c i)) (fun i => S (s i))
  exact (key _ σ' _
    (GlobalTheory.GroupExpansionLinear.expandsG_sum V D A G U F q l c (fun i => S (s i)) s σ' (fun i => hS _) (fun _ => rfl))
    (hlin l c (fun i => S (s i)) _ σ' (fun i => hΓ _) (fun _ => rfl))).symm

end GlobalTheory.PairingLinear
