import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnivChar
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ThetaTranslateRangeGap
import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedLiftUnipotentTypeBaseLevelForm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ProjectedThetaLiftExtremalVectorEqClassSum
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComplexFormsBaseLevelLeSpanIntegral
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links IsDedekindDomain NumberField Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.ExportSeries GlobalTheory.SeriesTie GlobalTheory.TwInputs GlobalTheory.TwSys GlobalTheory.TwAll GlobalTheory.SupLaw GlobalTheory.LiftLeaf
open Formalism.MainNotions.IntegralHeckeForms (TwOK ClsQ HkIdx V0 Fm0 FullRk SgJ BasisOf)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TypeClassSum

set_option maxHeartbeats 1600000 in

theorem goodModel_eq_classSum : ∀ (D : D7) (X : RealSide D) (E : IntegralHeckeForms.XD D) (Y : SerSide X E), (∀ j t, GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.GoodRangeAt X.R.toRealDat j t) →
    ∀ i, BaseTup Y i → ∀ (j : Fin D.R.m) (b : Bool), ∀ w ∈ GlobalTheory.IndefiniteRowSideFullHecke.ThetaTranslateSize.goodModel X.R.toRealDat j,
      (∀ (u : G0g D.nd) (hu : u ∈ D.nexp.U) (κ : GA D (Wc D j)),
        Lev.IsLevelLift (Wc D j) (Y.Z.ρ.B i j b).F.βT (Y.Z.ρ.B i j b).G.levT (Y.Z.ρ.eG i j b u) κ → ∀ g,
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) (g * κ) =
          Y.Z.ρ.e i b ((D.nexp.psiU i b ⟨u, hu⟩ : (FractionRing (D.ntw.O i))ˣ) : FractionRing (D.ntw.O i)) *
          (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) g) →
      ∃ F ∈ Submodule.span ℂ (Y.Z.ρ.mt i j b 0 ∅ 1 : Set (Bridge.Gf (Vc D j) → PolF D (Wc D j).rank (Vc D j).rank)),
        (X.R.HW j (sg0 D X.A3.A)).e w (X.geo.v₀ j _) = Y.Z.ρ.sum i j b 0 ∅ 1 F := by
  intro D X E Y hG i hB j b w hw hty
  obtain ⟨t, hxi, hQ⟩ := hB j b
  obtain ⟨y0, rfl⟩ : w ∈ LinearMap.range (X.R.thG j t) := by
    rw [hG j t]; exact hw
  obtain ⟨y, hlaw, heq⟩ := _root_.GlobalTheory.AvgLevel.avg_level D X E Y i j b t hxi hQ y0 hty
  obtain ⟨F, hF, hsum⟩ := _root_.GlobalTheory.LiftClassSum.exists_projected_thetaLift_eq_sum D X E Y i j b t hxi hQ y hlaw
  exact ⟨F, _root_.GlobalTheory.BaseSpan.formsC_le_span_mt D X E Y i j b F hF, heq.symm.trans hsum⟩

end GlobalTheory.TypeClassSum
