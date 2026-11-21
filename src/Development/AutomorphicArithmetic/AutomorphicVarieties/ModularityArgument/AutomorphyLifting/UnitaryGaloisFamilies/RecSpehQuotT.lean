import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.UnitaryGaloisFamilies.IrrCaseT
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.TotalReciprocity
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalLanglandsSpehProduct
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SumSegmentsLanglands

open UpperTheory.V.Af UpperTheory.V.Af.Gu UpperTheory.V.Z.Win UpperTheory.V.Z.Win.Gu
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.WeilDeligne GlobalTheory.LocLanglands
open GlobalTheory.CuspRep GlobalTheory.DefiniteBC UpperTheory.Zero.LLC

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem segSum_nu {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hnu : ∀ x (s : ℝ), rc (x.nu s) = (rc x).lpTw s)
    (l : List (Segment (w.adicCompletion E))) (c : ℝ) :
    segSum rc (l.map fun Γ => Γ.nu (c : ℂ)) = (segSum rc l).lpTw c := by
  simp only [segSum]
  rw [← GlobalTheory.NuShift.sumList_lpTw, List.map_map, List.map_map]
  congr 1
  refine List.map_congr_left fun Γ _ => ?_
  show ((rc (Γ.first.nu (c : ℂ))).lpTw _).lpChar _ = _
  rw [hnu, WD.lpTw_add, add_comm, ← WD.lpTw_add, GlobalTheory.NuShift.lpChar_lpTw]
  rfl

private theorem rec_spehQuotT {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}
    {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRecT h rc) (hTZ : GlobalTheory.Published.GenericUnitaryDualGL)
    (hLM : GlobalTheory.Published.StandardCosocleGL) (a d n : ℕ) (hd : ∑ _ : Fin d, a = n) (σ : LocIrr w a) (σ' : LocIrr w n)
    (hu : IsUnitarisable σ.ρ) (hg : IsGeneric σ.ρ) (hq : IsSpehQuot hd σ σ') :
    rc (cls (ParLaws.toRep σ')) =
      sumList ((List.range d).map fun k : ℕ => (rc (cls (ParLaws.toRep σ))).lpTw (((d : ℝ) - 1) / 2 - k)) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨m, δ, Δ, s, hΔ, hδu, hs, hd0, hφ⟩ := hTZ.exists_prod σ.smooth σ.irred hu hg
  have hA := _root_.GlobalTheory.isL_of_irreducible_prod_unitarisable_nu _ (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) a _ σ.ρ σ.irred m δ Δ s hΔ hδu hs hd0 hφ
  have hB := _root_.GlobalTheory.speh_quotient_isL _ hLM (GlobalTheory.T.unitarisable_segment_twist_precedes_add_one_le _) (GlobalTheory.T.parabolicInduction_in_stages_product_of_products _) a _ σ.ρ m δ Δ s hΔ hδu hs hd0 hφ d n hd _ σ'.ρ σ'.irred hq
  obtain ⟨a', ha', L⟩ := hrc
  rw [L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hB (equivRep (ParLaws.toRep σ'))),
    L.langlands _ _ (GlobalTheory.SpehRec.isL_of_equiv hA (equivRep (ParLaws.toRep σ)))]
  simp only [segSum]
  rw [List.map_flatMap, GlobalTheory.SpehRec.sumList_flatMap]
  congr 1
  refine List.map_congr_left fun i _ => ?_
  exact segSum_nu L.nu _ _

