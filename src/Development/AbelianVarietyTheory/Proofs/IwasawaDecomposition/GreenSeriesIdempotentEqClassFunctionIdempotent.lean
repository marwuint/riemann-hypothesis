import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TypeIdempotentCoeffAcrossLayers
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinsumCentralIdempotentOfIrrCharacterEqSimple
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CuspidalLabelPolynomialUniqueAllPrimes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsBlocksOfCuspidalCharacterList
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LabelMapLabelOfClassFunctionLabel

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial

theorem GlobalTheory.SerCmp.eSerC_eq_eSerO : GlobalTheory.Published.GreenCuspidal → ∀ (g : ℕ) [Fact g.Prime] (L : GlobalTheory.GLq.LabelDatum g) (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y) (hζ : IsGenSys L.gen), t = L.teich → ∀ O : Formalism.IrreducibleCountingLemmas.TYPES.LabelMap (ZMod g) (convC t ht L.gen hζ), (∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple τ → Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) τ → Formalism.IrreducibleCountingLemmas.TYPES.HasCuspLabel (convC t ht L.gen hζ) τ (O.lab d τ)) → ∀ (r : ℕ) (f : (ZMod g)[X]), 1 ≤ r → GlobalTheory.GLq.eSerC L r f = eSerO O r f := by
  intro hG g _ L t ht hζ htL O hO r f hr
  have hcusp : ∀ (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → CategoryTheory.Simple V →
      Formalism.IrreducibleCountingLemmas.TYPES.IsCuspidal (ZMod g) V → GlobalTheory.GLq.IsCuspOf L (O.lab d V) (fun x => V.character x) :=
    fun d V hd hs hc => _root_.GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel g L t ht hζ htL d V _ hd ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc)
      (hO d V hd hs hc)
  have hB : ∀ τ : FDRep ℂ (GL (Fin r) (ZMod g)), CategoryTheory.Simple τ →
      (GlobalTheory.GLq.HasLabel L (fun x => τ.character x) f ↔ Formalism.IrreducibleCountingLemmas.TYPES.HasLabelO O τ f) := by
    intro τ hτ
    constructor
    · refine _root_.GlobalTheory.SerCmp.hasLabelO_of_hasLabel g L O (fun d V P hd hs hc hP => ?_) (fun d χ hχ => ?_)
        (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) (_root_.GlobalTheory.SerCmp.canonList_of_cuspidal_list g) r τ f hτ
      · exact _root_.GlobalTheory.GLq.isCuspOf_label_unique_allPrimes hG g L d P (O.lab d V) _ hP (hcusp d V hd hs hc)
      · obtain ⟨V, hV, hVχ⟩ := hχ.2.1
        have hχV : (fun x => V.character x) = χ := funext hVχ
        have hd : 1 ≤ d := hχ.1
        exact ⟨V, hV, (_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hV).1 (hχV ▸ hχ), hVχ⟩
    · exact _root_.GlobalTheory.SerCmp.hasLabel_of_hasLabelO g L O hcusp (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) r τ f hτ
  unfold GlobalTheory.GLq.eSerC Formalism.L2.NT.eSerO
  rw [_root_.GlobalTheory.SerCmp.finsum_zOf_eq_finsum_zIdem]
  refine finsum_congr fun z => finsum_congr_Prop (propext ?_) fun _ => rfl
  constructor
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).1 hl⟩
  · rintro ⟨τ, hτ, hz, hl⟩
    exact ⟨τ, hτ, hz, (hB τ hτ).2 hl⟩
