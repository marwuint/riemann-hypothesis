import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MonodromyVanishesWeilTwistIff
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsGoodConjSelfDualTwistSplitUnramified
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsUnitaryTwistAbsPow
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CuspRepSatakeIffLocalComponentSatake
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsTemperedGLOfHasSatGL
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AutomorphicFormsFiniteGL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalArtinExistsHolds
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsSteinberg
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsSstAtOfIsCrysAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaloisHodgeOfCuspidal
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.PhiTwist

open GlobalTheory.GalCut.IwaTwist GlobalTheory.GalCut7.IwahoriTwist UpperTheory.V UpperTheory.V.Af ValuativeRel

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}

theorem loc_eq_unrChar [IsTotallyComplex E] (χ : HChar E) (hu : χ.UnrAt w) :
    χ.loc w = SmGL.unrChar (w.adicCompletion E) (χ.val w) := by
  refine MonoidHom.ext fun x => ?_
  have h2 := unif_spec w
  have h0 : Valued.v (x : w.adicCompletion E) ≠ 0 := by simp
  have h1 : IsUnitAt w (x * (atFin w (unif w) ^ ord (w.adicCompletion E) x)⁻¹) := by
    unfold IsUnitAt IsUnifAt at *
    rw [Units.val_mul, Units.val_inv_eq_inv_val, Units.val_zpow_eq_zpow_val, map_mul,
      map_inv₀, map_zpow₀, h2, ← WithZero.exp_zsmul, SphCompletion.ord_completion]
    simp only [smul_eq_mul, mul_neg, mul_one, neg_neg]
    rw [WithZero.exp_log h0, mul_inv_cancel₀ h0]
  have h3 := hu _ h1
  rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h3
  exact h3

theorem satWD_map_mul (h : Formalism.ConjugateSelfDual.IsPlaceOver A w) (a : ℕ) (B : Multiset ℂˣ) (c : ℂˣ)
    {art : Weil h →* (w.adicCompletion E)ˣ} (ha : IsLocalArtin h art)
    (hs : GlobalTheory.WeilDeligne.IsSmooth ((SmGL.unrChar (w.adicCompletion E) c).comp art)) :
    satWD h a (B.map (· * c)) = (satWD h a B).lpTwist _ hs := by
  have hM : WD.lpOfChar h ((SmGL.unrChar (w.adicCompletion E) c).comp art) hs =
      WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹) := Test.lpOfChar_unrChar ha c hs
  have hMu : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).unr := (WD.unr_mk _).mpr (WDRep.unr_diag _)
  have hMf : (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)).frobEig = {((c⁻¹ : ℂˣ) : ℂ)} := by
    rw [WD.frobEig_diag]; simp
  have h0 : (0 : ℂ) ∉ B.map fun b => ((b⁻¹ : ℂˣ) : ℂ) := by
    simp
  obtain ⟨hu0, hf0, -⟩ := WD.lpUnr_spec (h := h) _ h0
  have hU : WD.lpUnr h ((B.map (· * c)).map fun b => ((b⁻¹ : ℂˣ) : ℂ)) =
      (WD.lpUnr h (B.map fun b => ((b⁻¹ : ℂˣ) : ℂ))).lpChar (WD.mk (WDRep.diag h fun _ : Fin 1 => c⁻¹)) := by
    have hu1 := WD.unr_lpChar _ _ hu0 hMu
    rw [WD.unr_eq_lpUnr _ hu1, WD.frobEig_char _ _ _ hu0 hMu hMf, hf0, Multiset.map_map, Multiset.map_map]
    congr 1
    refine Multiset.map_congr rfl fun b _ => ?_
    simp [mul_inv_rev, mul_comm]
  rw [← lpChar_lpOfChar, hM, satWD, satWD, GlobalTheory.NuShift.lpChar_lpTw, hU]

end GlobalTheory.RoadU.PhiTwist

end
