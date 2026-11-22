import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MeasAtOf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.QuotMeasureEqSmul
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HcFiniteAndSchurMult
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.CuspFormsRapidDecay
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ProdLowestKTypeDimsIndepComplexEmbedding
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Pj Formalism.IndefR.Links Formalism.IndefR.FWT
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.AllWt GlobalTheory.CompHt GlobalTheory.BigTop GlobalTheory.CovTop GlobalTheory.CovTop.MeasRd
open Formalism.MainNotions
open MeasureTheory Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR.Mult Formalism.BasicNotions.TH Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.ExactRatioProof

open scoped InnerProductSpace ComplexConjugate

theorem L1 : ∀ (D : D7) (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (∏ ρ, ((dimK _ _ (kapAt (Wc D i) σ ρ) : ℚ) : ℂ)) = ((∏ τ, GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.dimAt D i τ : ℝ) : ℂ) := _root_.GlobalTheory.DimProdLab.prod_dims

theorem K2aux (D : D7) (T : CoreJ D) (h : LawsJ T) (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ) (hs : GoodEmb T.Q.c s)
    (f : FDSec (T.U ((i : ℕ) + 1) s).X) (W : HSp D) (hV : T.V ((i : ℕ) + 1) s = W) :
    eLpNorm (fun q : AutQ W => ‖(hV ▸ ((lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) : ℂ) •
      adel (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s)
        (muPin (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (T.mu ((i : ℕ) + 1) s) (T.cE ((i : ℕ) + 1) s)) f) :
          GA D W → ℂ) q.out‖) 2 (muQ1 W) =
      ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) *
        petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s))
          (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f := by
  subst hV
  have hj : InR D ((i : ℕ) + 1) := ⟨Nat.le_add_left _ _, i.2⟩
  have hmu := h.muUnit _ hj s hs
  have hcu := h.cUnit _ hj s hs
  set c := lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i) with hcdef
  have hc0 : 0 < c := lieFacZ_pos _ _
  unfold petE
  rw [← Real.enorm_eq_ofReal hc0.le, ← eLpNorm_const_smul]
  refine eLpNorm_congr_norm_ae (Filter.Eventually.of_forall fun q => ?_)
  simp only [Pi.smul_apply, smul_eq_mul, norm_norm, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos hc0, adel_muPin]
  rw [hcu, hmu.2.1]
  simp only [abs_one, one_mul, abs_norm, abs_of_nonneg (ptN_nonneg _ _ _)]
  unfold ptN
  rw [pnorm_eq_of_unit _ _ _ _ (hmu.2.2.2 _)]

theorem K2 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ (hV : T.V ((i : ℕ) + 1) s = Wc D i) (f : FDSec (T.U ((i : ℕ) + 1) s).X), eLpNorm (fun q : AutQ (Wc D i) => ‖GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.adFun T i hV f q.out‖) 2 (muQ1 (Wc D i)) = ENNReal.ofReal (lieFacZ (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) * petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f :=
  fun D T h i s hs hV f => K2aux D T h i s hs f (Wc D i) hV

theorem K3 : ∀ (D : D7) (T : CoreJ D), LawsJ T → ∀ (i : Fin D.R.m) (s : T.Q.c.F →+* ℂ), GoodEmb T.Q.c s → ∀ f ∈ GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.scalarForms T i s, petE (T.V ((i : ℕ) + 1) s) (T.dict ((i : ℕ) + 1) s) (muQ1 (T.V ((i : ℕ) + 1) s)) (modelWt (T.U ((i : ℕ) + 1) s) (GlobalTheory.IndefiniteRowSideFullHecke.OneMeasureSizes.expW D i)) f ≠ ⊤ := by
  intro D T h i s hs f hf
  obtain ⟨th, hr, -, hdu⟩ := h.dictU _ ⟨Nat.le_add_left _ _, i.2⟩ s hs
  exact petE_ne_top _ _ _ prob_le_one hdu.2.2.2.1 hf

end GlobalTheory.ExactRatioProof
