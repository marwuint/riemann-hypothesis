import Development.AbelianVarietyTheory.Proofs.SatakeParameters.NormEqOfSamePlace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Adm2OfHyp
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CmGaloisRepresentationCrystalline
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TypeConditions.UnrRecOfHasSat

noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.GalS.Prod

open GlobalTheory GlobalTheory.GalFirstClause Formalism.BasicNotions.Loc GlobalTheory.Pst GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.GalOfCusp GlobalTheory.HeckeGal

theorem norm_algHom {l : ℕ} [Fact l.Prime] {K L : FinExt l} (τ : ↥K.1 →ₐ[ℚ_[l]] ↥L.1) (y : ↥K.1) :
    ‖((τ y : ↥L.1) : Om l)‖ = ‖(y : Om l)‖ := by
  have e1 : minpoly ℚ_[l] ((τ y : ↥L.1) : Om l) = minpoly ℚ_[l] y :=
    minpoly.algHom_eq (L.1.val.comp τ) (L.1.val.comp τ).toRingHom.injective y
  have e2 : minpoly ℚ_[l] (y : Om l) = minpoly ℚ_[l] y := minpoly.algHom_eq K.1.val K.1.val.toRingHom.injective y
  rw [← PadicAlgCl.spectralNorm_eq, ← PadicAlgCl.spectralNorm_eq, spectralNorm, spectralNorm, e1, e2]

theorem induces_of_isInduced {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]
    [IsAlgClosure E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] {Bw : LocBridge l E Ω (Dec (F := E) A) O}
    (hj : Induces Bw) {τ : E →+* Om l} {LL' : FinExt l} {τ' : ↥Bw.Kw.1 →ₐ[ℚ_[l]] ↥LL'.1} (hτ : IsInduced Bw τ τ')
    (x : 𝓞 E) : ‖τ (x : E)‖ < 1 ↔ x ∈ w.asIdeal := by
  rw [hτ, norm_algHom]
  exact (hj.valuation_lt_one_iff _).symm.trans (h x)

theorem core (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) {a : ℕ}
    (π : D.naut.CG a) [IsCMField D.host.E] (π₀ : CuspSub D.host.E a)
    (hmk : CG.mk π₀ = (P.cg.e a π).1) {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ}
    {χ : HChar (maximalRealSubfield D.host.E)} {r : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (D.host.E →+* Qbar l) → Multiset ℤ} (H : IsGalU π₀ χ ι r wt HT) :
    (∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2)))) := by
  have hloc0 : ∀ w : PlE D.host, P.T.e w (D.naut.locG π w) = ParLaws.locPar hL (CG.mk π₀) (D.nd.plOm.2 w) := fun w => by
    rw [P.cg.loc, hmk]
    rfl
  have haw : ∀ (w : PlE D.host) (hl : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal),
      Aw (wdOf (D.nd.plOm.2 w) hl ι r) (P.T.e w (D.naut.lpTw (D.naut.locG π w) ((1 - (a : ℝ)) / 2))) := fun w hl => by
    obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF _ a π₀ w
    rw [P.T.tw, hloc0, ParLaws.locPar_mk hL hσ]
    exact H.aw hl (ParLaws.isRec_locRec hL _) hσ
  exact haw

end UpperTheory.GalS.Prod
