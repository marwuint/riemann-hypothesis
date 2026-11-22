import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFractionFieldExtensionOfMaps
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsCuspExpansionAtInfinityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInjectiveCuspExpansionRingHom
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCoeffConj
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneGermRingHomAndRestrict
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.UpperHalfPlaneCodiscreteGermIdentityAndUnits
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModularFunctionRingOverIsDomain
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExpTwoPiIRatInFieldRootsOfUnityProperties
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsRingEquivCompGLTwoPosRatFun
open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

namespace GlobalTheory.FN

theorem frac_nonempty : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ),
    Nonempty (Frac Ω ε) := by
  intro Ω _ _ _ ε
  classical
  haveI : IsDomain (ring ε.range) := _root_.GlobalTheory.FN.ring_isDomain ε.range
  obtain ⟨hmem, hconst⟩ := _root_.GlobalTheory.FN.mem_ring_iff_inR ε.range
  obtain ⟨-, huniq, hC, -, -⟩ := _root_.GlobalTheory.FNExp.exp_props Ω ε
  obtain ⟨e, he_inj, he_exp⟩ := _root_.GlobalTheory.FN.expansion_injective_ringHom Ω ε
  obtain ⟨hexp_mem, -, -, -, -, -⟩ := _root_.GlobalTheory.FNRoots.main Ω ε
  obtain ⟨⟨G, hG⟩, hmd, -, -, hHs⟩ := _root_.GlobalTheory.FN.germ_ringHom_and_restrict
  obtain ⟨-, hid, hunit⟩ := _root_.GlobalTheory.FN.germ_main

  let cst : Ω →+* ring ε.range :=
    { toFun := fun x => ⟨fun _ => ε x, (hmem _).2 (hconst _ ⟨x, rfl⟩)⟩
      map_one' := Subtype.ext (funext fun _ => by simp)
      map_mul' := fun x y => Subtype.ext (funext fun _ => by simp)
      map_zero' := Subtype.ext (funext fun _ => by simp)
      map_add' := fun x y => Subtype.ext (funext fun _ => by simp) }
  have hcst : ∀ x, ((cst x : ring ε.range) : ℍ → ℂ) = fun _ => ε x := fun _ => rfl
  have hec : ∀ x, e (cst x) = algebraMap Ω (HahnSeries ℚ Ω) x := by
    intro x
    refine huniq _ _ _ (he_exp (cst x)) ?_
    convert hC x using 1
    · rfl
    · simp [HahnSeries.algebraMap_apply']

  have hsl := fun g : GQ => _root_.GlobalTheory.FN.cmp_ringEquiv ε.range g hexp_mem
  choose σ hσ using hsl
  have hslc : ∀ g x, σ g (cst x) = cst x := by
    intro g x
    apply Subtype.ext
    rw [hσ]
    rfl

  have hga := fun s : Ω ≃ₐ[ℚ] Ω => _root_.GlobalTheory.FN.exists_ringEquiv_coeff_conj Ω ε s.toRingEquiv
  choose τ hτ using hga

  let A : ring ε.range →+* Mero := G.comp (ring ε.range).subtype
  have hA : ∀ a : ring ε.range, A a = ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) := fun a => hG a
  have hdiff : ∀ a : ring ε.range, DifferentiableOn ℂ (up (a : ℍ → ℂ)) Hs :=
    fun a => (hmd _).1 (_root_.GlobalTheory.FN.inR_mdifferentiable _ _ ((hmem _).1 a.2))
  have hAunit : ∀ a, a ≠ 0 → IsUnit (A a) := by
    intro a ha
    rw [hA]
    refine (hunit _ (hdiff a) ?_).2
    intro h0
    apply ha
    have h0' : ((up (a : ℍ → ℂ) : ℂ → ℂ) : Mero) = ((up ((0 : ring ε.range) : ℍ → ℂ) : ℂ → ℂ) : Mero) := by
      rw [h0, ← hA, map_zero]
    have heq := hid _ _ (hdiff a) (hdiff 0) h0'
    apply Subtype.ext
    funext t
    have := heq t (hHs t)
    simpa [up, UpperHalfPlane.ofComplex_apply] using this
  obtain ⟨K, fK, aK, io, e', sl', ga', A', hinj, hsurj, hioc, he', hsl', hga', hA'⟩ :=
    _root_.GlobalTheory.fraction_field_extension Ω (ring ε.range) (HahnSeries ℚ Ω) Mero GQ (Ω ≃ₐ[ℚ] Ω) cst e σ τ A he_inj hec hslc hAunit
  refine ⟨{
    K := K
    fld := fK
    alg := aK
    io := io
    io_inj := hinj
    io_surj := hsurj
    io_c := fun x a ha => ?_
    exp := e'
    exp_io := fun a => ?_
    sl := sl'
    sl_io := fun g a a' ha => ?_
    gal := ga'
    gal_exp := fun s f r => ?_
    an := A'
    an_io := fun a => ?_ }⟩
  · have : a = cst x := Subtype.ext ha
    rw [this, hioc]
  · rw [he']
    exact he_exp a
  · rw [hsl']
    congr 1
    exact Subtype.ext ((hσ g a).trans ha.symm)
  · obtain ⟨Φ, hΦ⟩ := _root_.GlobalTheory.FNTwist.exists_scale_twist_ringHom Ω Ω (s : Ω →+* Ω) 1 (fun _ => 1) one_pos rfl (fun _ _ => (mul_one 1).symm)
    have hΦ' : ∀ h r, (Φ h).coeff r = s (h.coeff r) := by
      intro h r
      have := hΦ h r
      simpa using this
    have key : ∀ a, e' (ga' s (io a)) = Φ (e' (io a)) := by
      intro a
      rw [hga', he', he']
      ext r
      rw [hτ s a (e a) (e (τ s a)) (he_exp a) (he_exp _) r, hΦ']
      rfl
    obtain ⟨a, b, hb, hf⟩ := hsurj f
    have hib : io b ≠ 0 := fun h => hb (hinj (by rw [h, map_zero]))
    have hf' : f = io a * (io b)⁻¹ := by rw [← hf, mul_assoc, mul_inv_cancel₀ hib, mul_one]
    have hfe : e' (ga' s f) = Φ (e' f) := by
      rw [hf']
      simp only [map_mul, map_inv₀, key]
    rw [hfe, hΦ']
  · rw [hA', hA]
    rfl

end GlobalTheory.FN
