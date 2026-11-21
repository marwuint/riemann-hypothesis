import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesOfIsSubquotient
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsConstituentOfRepIsoLeft
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MonodromyTrivialEverywhere
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TameParameterCoupled
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalOfIsCuspidal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormalizedAbsValueLocalFieldUnitMapHomeomorph
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ParabolicInductionCompGeneralLinearGroupMapOfFie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsRecLawsSuppUnitSurj
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LabLPIsLabelActK
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCuspidalSupportIrreducibleSmoothGL
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HasFiniteLengthOfIsIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.UnlinkedProductIrreducible
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.DepthZeroJacquetInjective
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterIffIsCuspidalGLnFiniteField
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoeffZeroNeOfMonicIrr
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LabelDatum
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.GreenCuspidalIff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CanonListLength
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCuspidalCharacterOfPolynomialOfCuspidalLabel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.TraceHarishChandraInducedEqProductCharacters
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsConstituentHarishChandraRepIffPairingNeZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ClassFunctionLabelOfLabelMapLabel

noncomputable section

namespace GlobalTheory.RegType

section Fin

open Polynomial GlobalTheory.GLq Formalism.IrreducibleCountingLemmas.TYPES Formalism.L2.NT CategoryTheory

variable {g : ℕ} [Fact g.Prime]

def datum (t : Formalism.CyclotomicNorms.Fbar g →* ℂ) (ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y)
    (ζ : ℕ → Formalism.CyclotomicNorms.Fbar g) (hζ : IsGenSys ζ) : LabelDatum g where
  teich := t
  teich_inj := ht
  gen := ζ
  gen_order d hd := (hζ d hd).1
  gen_norm d e hd he := (hζ d hd).2 (d * e) (dvd_mul_right d e) (Nat.mul_pos hd he)

variable {t : Formalism.CyclotomicNorms.Fbar g →* ℂ} {ht : ∀ x y : Formalism.CyclotomicNorms.Fbar g, x ≠ 0 → y ≠ 0 → t x = t y → x = y}
  {ζ : ℕ → Formalism.CyclotomicNorms.Fbar g} {hζ : IsGenSys ζ} (O : LabelMap (ZMod g) (convC t ht ζ hζ))
  (hO : ∀ (d : ℕ) (τ : FDRep ℂ (GL (Fin d) (ZMod g))), 1 ≤ d → Simple τ → IsCuspidal (ZMod g) τ →
    HasCuspLabel (convC t ht ζ hζ) τ (O.lab d τ))
include hO

theorem isCuspOf_lab (d : ℕ) (V : FDRep ℂ (GL (Fin d) (ZMod g))) (hd : 1 ≤ d) (hs : Simple V)
    (hc : IsCuspidal (ZMod g) V) : IsCuspOf (datum t ht ζ hζ) (O.lab d V) (fun x => V.character x) :=
  _root_.GlobalTheory.SerCmp.LabConv.isCuspOf_of_hasCuspLabel g (datum t ht ζ hζ) t ht hζ rfl d V _ hd ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hd hs).2 hc) (hO d V hd hs hc)

theorem allLab : AllLab (datum t ht ζ hζ) := by
  intro d χ hχ
  obtain ⟨V, hV, hVχ⟩ := hχ.2.1
  obtain rfl : (fun x => V.character x) = χ := funext hVχ
  exact ⟨_, isCuspOf_lab O hO d V hχ.1 hV ((_root_.GlobalTheory.CuspCharRep.isCusp_character_iff_isCuspidal g d V hχ.1 hV).1 hχ)⟩

theorem eSerC_mul_zIdem {r : ℕ} (ρ : FDRep ℂ (GL (Fin r) (ZMod g))) (hρ : Simple ρ) (f : (ZMod g)[X])
    (h : zIdem ρ * eSerO O r f = zIdem ρ) : eSerC (datum t ht ζ hζ) r f * zIdem ρ = zIdem ρ := by
  classical
  by_cases hm : zIdem ρ ∈ GlobalTheory.SerOSys.Zl O r f
  · obtain ⟨τ, hτ, he, hl⟩ := hm
    have h1 := _root_.GlobalTheory.SerCmp.hasLabel_of_hasLabelO g (datum t ht ζ hζ) O (isCuspOf_lab O hO) (_root_.GlobalTheory.HCChar.trace_hcRep_eq_hcL g) (_root_.GlobalTheory.GLq.ConstIff.constituent_hcRep_iff g) r τ f hτ hl
    have h2 : zOf (fun x => τ.character x) = zIdem τ := by
      unfold zOf zIdem
      simp only [FDRep.char_one]
      rfl
    have h3 := eSerC_mul_zOf (datum t ht ζ hζ) ⟨τ, hτ, fun _ => rfl⟩ h1
    rwa [h2, he] at h3
  · have h0 : zIdem ρ = 0 := by
      rw [← h, GlobalTheory.SerOSys.eSerO_eq_sum, Finset.mul_sum]
      refine Finset.sum_eq_zero fun z hz => ?_
      have hz' := (GlobalTheory.SerOSys.Zl_finite O r f).mem_toFinset.1 hz
      rw [GlobalTheory.SerOSys.mul_of_mem ⟨ρ, hρ, rfl⟩ (GlobalTheory.SerOSys.Zl_sub O r f hz'), if_neg]
      rintro e
      exact hm (e ▸ hz')
    rw [h0, mul_zero]

end Fin

section Loc

open Polynomial GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.GLp.Supp GlobalTheory.SerSys NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal
  GlobalTheory.WeilDeligne GlobalTheory.LocGL GlobalTheory.LocLanglands GlobalTheory.SmGL GlobalTheory.PRep GlobalTheory.SplitRead GlobalTheory.PendOf ValuativeRel GlobalTheory.StepData

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {g : ℕ} [Fact g.Prime] {E : Type} [Field E] [NumberField E] {w : HeightOneSpectrum (𝓞 E)}
  (hw : ((g : ℕ) : 𝓞 E) ∈ w.asIdeal) (i : ℚ_[g] ≃+* w.adicCompletion E) (hi : Continuous i)

theorem val_lt_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y < 1 ↔ ‖y‖ < 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.lt_one_iff_lt_one, Valued.toNormedField.norm_lt_one_iff]

theorem val_le_iff (y : w.adicCompletion E) : valuation (w.adicCompletion E) y ≤ 1 ↔ ‖y‖ ≤ 1 := by
  have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := isEquiv (valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  rw [he.le_one_iff_le_one, Valued.toNormedField.norm_le_one_iff]

include hi in
theorem val_int_le (z : ℤ_[g]) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) ≤ 1 :=
  (val_le_iff _).2 (GlobalTheory.TypeRec.Model.emb_le w g i.toRingHom hi _ z.2)

include hw hi in
theorem val_int_lt (z : ℤ_[g]) (hz : PadicInt.toZMod z = 0) : valuation (w.adicCompletion E) (i (z : ℚ_[g])) < 1 := by
  have h1 : z ∈ RingHom.ker (PadicInt.toZMod (p := g)) := hz
  rw [PadicInt.ker_toZMod, PadicInt.maximalIdeal_eq_span_p, Ideal.mem_span_singleton'] at h1
  obtain ⟨c, rfl⟩ := h1
  rw [PadicInt.coe_mul, map_mul, map_mul, PadicInt.coe_natCast, map_natCast]
  exact mul_lt_one_of_nonneg_of_lt_one_right (val_int_le i hi c) zero_le
    ((val_lt_iff _).2 (Formalism.BasicNotions.Examples₂.LocF.norm_l_lt w g hw))

include hw hi in

theorem act_lift {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x)
    (k : GL (Fin n) ℤ_[g]) (h : GL (Fin n) (w.adicCompletion E)) (hh : IsLiftN (red g n k) h) :
    π h x = π (Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k)) x := by
  set K := Matrix.GeneralLinearGroup.map i.toRingHom (inc g n k) with hK
  have h1 : IntM (K⁻¹).val := fun a b => by
    rw [hK, ← map_inv, ← map_inv]
    exact val_int_le i hi ((k⁻¹).val a b)
  have h2 : MaxM (h.val - K.val) := fun a b => by
    have e1 := hh a b
    rw [dif_pos ⟨a.2, b.2⟩] at e1
    have e2 := val_int_lt hw i hi ((((red g n k).val a b).val : ℤ_[g]) - k.val a b) (by
      rw [map_sub, map_natCast, ZMod.natCast_zmod_val, sub_eq_zero]; rfl)
    have e3 := Valuation.map_add_lt _ e1 e2
    convert e3 using 2
    rw [PadicInt.coe_sub, map_sub, PadicInt.coe_natCast, map_natCast, Matrix.sub_apply]
    change _ - i (k.val a b : ℚ_[g]) = _
    ring
  have h3 : π (K⁻¹ * h) x = x := hx _ fun a b => by
    have e := h1.mul_maxM h2 a b
    rw [Matrix.mul_sub, ← Units.val_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.sub_apply,
      Matrix.one_apply] at e
    exact e
  conv_rhs => rw [← h3]
  rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]

include hw hi in
theorem mem_principalCongruenceFixed_of_levelOne {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x) :
    x ∈ fixK1 (π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) := by
  refine (Model.mem_principalCongruenceFixedVectors_iff _ _).2 fun k hk => ?_
  have := act_lift hw i hi π hx k 1 (fun a b => by
    rw [dif_pos ⟨a.2, b.2⟩, hk]
    by_cases hab : a = b
    · subst hab; simp [ZMod.val_one]
    · simp [Matrix.one_apply_ne hab])
  rw [map_one] at this
  exact this.symm

include hw hi in
theorem actK_ne_of_notKilled {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) (w.adicCompletion E)) V) {x : V} (hx : IsLevelOne π x)
    (z : MonoidAlgebra ℂ (Gn g n)) (hz : NotKilled π z x) :
    actK (π.comp (Matrix.GeneralLinearGroup.map i.toRingHom)) z x ≠ 0 := by
  obtain ⟨ℓ, hℓ, h0⟩ := hz
  rw [Finsupp.sum_fintype _ _ (fun _ => by simp)] at h0
  rw [actK, LinearMap.sum_apply]
  convert h0 using 2 with y
  have e : red g n (Function.invFun (red g n) y) = y := Function.invFun_eq (Model.red_surjective n y)
  rw [LinearMap.smul_apply, act_lift hw i hi π hx (Function.invFun (red g n) y) (ℓ y) (by rw [e]; exact hℓ y)]
  rfl

theorem has_of_actK (S : Sys g) {n : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin n) ℚ_[g]) V) {x : V} (hx : x ∈ fixK1 π) {z : MonoidAlgebra ℂ (Gn g n)}
    (hz : actK π z x ≠ 0) {f : (ZMod g)[X]} (he : S.e n f * z = z) : Has S π f := by
  refine ⟨_, ((repK π).asAlgebraHom z ⟨x, hx⟩).2, ?_⟩
  rw [← repK_alg π (S.e n f) ((repK π).asAlgebraHom z ⟨x, hx⟩), ← Module.End.mul_apply, ← map_mul, he, repK_alg]
  exact hz

variable {Ω : Type} [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {A : ValuationSubring Ω} {h : IsPlaceOver A w}
  {rc : IrrGL (w.adicCompletion E) → WD h} (hrc : IsRec h rc) (hDZ : GlobalTheory.Published.DepthZeroInertia)
  (κ : IsLocalRing.ResidueField A ≃+* Formalism.CyclotomicNorms.Fbar g) (L : LabelDatum g) (h5 : 5 ≤ g) (hA : AllLab L)
  {t : G E Ω} (ht : t ∈ Ine (F := E) A) (hκ : Formalism.L2.NT.TameCoupled A κ t L.gen)
include hi hrc hDZ ht hκ

end Loc

end GlobalTheory.RegType

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

end
