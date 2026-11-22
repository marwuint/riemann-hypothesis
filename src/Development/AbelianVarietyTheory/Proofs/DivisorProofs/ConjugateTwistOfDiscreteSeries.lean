import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SeriesRatSOf
import Development.AbelianVarietyTheory.Definitions.Divisors.LevelOfOfSameBut
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsAlgebraicOfRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesVecFlatEqSum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeSmallGeneration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EllipticCurveMapToAbelian
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoefficientPolynomialGLFunctionNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjTupleAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjFixAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TwistedConjCoefAt

set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.BigOn.Exp.TwConj

open GlobalTheory.ConjTwist

theorem scale_pow_eq {D : D7} {Γ : Type} [Group Γ] [Fintype Γ] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (Rl : RealDat3 D A3 Ks)
    (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) {j : Fin D.R.m} (B : Base (Vc D j) (Wc D j)) {c c' : ℂ}
    (h : IsScale Rl v₀ B c) (h' : IsScale Rl v₀ B c') : ∃ k : ℕ, k ≠ 0 ∧ c' ^ k = c ^ k := by
  obtain ⟨gR, cR0, cL0, hT, u, hu, hF⟩ := h
  obtain ⟨gR', cR0', cL0', hT', u', hu', hF'⟩ := h'
  obtain rfl : u' = u := funext fun τ => Subtype.ext ((hu' τ).trans (hu τ).symm)
  obtain ⟨a, ⟨k, hk, hak⟩, ha⟩ := _root_.GlobalTheory.CoefRoot.coef_root _ _ _ _ _ _ _ _ _ _ _ _ _ hT hT' j
  obtain ⟨F, x, hx⟩ := _root_.GlobalTheory.CoeffNonvanish.exists_coefFn_ne_zero (FWT.lamV D j)
  have e1 := hF' F
  rw [ha] at e1
  erw [LinearMap.map_smul, LinearMap.map_smul, hF F] at e1
  have e2 := congrFun e1 x
  simp only [Pi.smul_apply, smul_eq_mul] at e2
  have hc : c' = D.what₂.embLL a * c := (mul_right_cancel₀ hx ((mul_assoc _ _ _).trans e2)).symm
  exact ⟨k, hk, by rw [hc, mul_pow, ← map_pow, hak, map_one, one_mul]⟩

theorem root_mul {a b : ℂ} (ha : IsRoot1 a) (hb : IsRoot1 b) : IsRoot1 (a * b) := by
  obtain ⟨n, hn, ha⟩ := ha
  obtain ⟨m, hm, hb⟩ := hb
  exact ⟨n * m, Nat.mul_pos hn hm, by rw [mul_pow, pow_mul, ha, one_pow, mul_comm n, pow_mul, hb, one_pow, one_mul]⟩

theorem root_inv {a : ℂ} (ha : IsRoot1 a) : IsRoot1 a⁻¹ := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [inv_pow, ha, inv_one]⟩

theorem root_map (τ : ℂ ≃+* ℂ) {a : ℂ} (ha : IsRoot1 a) : IsRoot1 (τ a) := by
  obtain ⟨n, hn, ha⟩ := ha
  exact ⟨n, hn, by rw [← map_pow, ha, map_one]⟩

theorem root_ne {a : ℂ} (ha : IsRoot1 a) : a ≠ 0 := by
  obtain ⟨n, hn, ha⟩ := ha
  rintro rfl
  rw [zero_pow hn.ne'] at ha
  exact zero_ne_one ha

theorem root_charOf {D : D7} (a : Recip D D.nd.Om) {R : Type} [CommRing R] (f : R →+* ℂ) {ψ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* Rˣ}
    (h : IsOpen (ψ.ker : Set (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om))) (x : (AE D)ˣ) :
    IsRoot1 ((GlobalTheory.SeriesTie.charOf a f ψ x : Circle) : ℂ) := by
  obtain ⟨σ, hσ⟩ := a.exists_sym x
  have hfin : Finite (Formalism.ConjugateSelfDual.G D.host.E D.nd.Om ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ h
  have hn : ψ.ker.index ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h1 : ψ σ ^ ψ.ker.index = 1 := by rw [← map_pow]; exact ψ.ker.pow_index_mem σ
  refine ⟨_, Nat.pos_of_ne_zero hn, ?_⟩
  rw [charOf_eq a f h hσ hn h1, ← map_pow, ← Units.val_pow_eq_pow_val, h1, Units.val_one, map_one]

theorem root_delta {D : D7} {ρ : Setup D.ntw} (hρ : ρ.Good) (i : D.ntw.Tw) (j : Fin D.R.m) (b : Bool) (x : (AE D)ˣ) :
    IsRoot1 (((ρ.B i j b).de.chi x : Circle) : ℂ) := by
  rw [hρ.delta]
  refine root_charOf _ _ ?_ x
  have : (Formalism.MainNotions.BlochKatoReduction.Gen.psiAt b (D.ntw.delta i)).ker = (D.ntw.delta i).ker := by
    ext σ
    cases b <;> simp [Formalism.MainNotions.BlochKatoReduction.Gen.psiAt, MonoidHom.mem_ker]
  rw [this]
  exact D.ntw.delta_open i

theorem conjFun_gen {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
    {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec} {O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)}
    {ph : Fin D.R.m → ℂ} {j : Fin D.R.m} {B : Base (Vc D j) (Wc D j)} {ψ ψ' : Twist D Circle}
    (hn : 8 * D.R.f * D.R.r + 4 ≤ D.R.nV) (H : HasTuples T R κ v₀ O ph j B ψ ψ') (hB : B.Good) {ω : PairRep (Vc D j) (Wc D j)}
    (hω : B.IsWeil 1 ω) (hψ : ψ.Good) (hψ' : ψ'.Good) (hQ : B.admitted ψ.Q) (hQ' : B.admitted ψ'.Q)
    (hδ : ∀ s, IsRoot1 ((B.de.chi s : Circle) : ℂ)) (hr : ∀ s, IsRoot1 ((ψ'.chi s : Circle) : ℂ))
    {c : VsV D j ℂ →ₗ[ℂ] (R.cV j).W} {u : ∀ ρ, lowT (R.MW j (sg0 D A)) ρ} (hc : ExtC R j (inC (O j).c') (O j).c0' c)
    (hu : ∀ ρ, (u ρ : (R.MW j (sg0 D A)).sm ρ) = v₀ j (sg0 D A) ρ) {τ : ℂ ≃+* ℂ} (h1 : FixBase T R j τ) (h2 : FixDat B τ)
    (h3 : ConjChar τ ψ ψ') {h : GA D (Vc D j)} (hh : h ∈ GfC (Vc D j)) {x x' : VsV D j ℂ} (hx : ConjVec j τ x x') :
    ∃ ζ : ℂ, IsRoot1 ζ ∧ ConjFun (O j) (κ j) τ ζ (ph j • B.gen ω ψ h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x)))
      (ph j • B.gen ω ψ' h (R.ioP j (PiTensorProduct.tprod ℂ u) (c x'))) := by
  obtain ⟨T0', A', R', F', v₀', O', k1, k2, k3, k4, k5, k6, k7, k8, k9, k10, k11, t, t', ht, ht'⟩ := H
  obtain ⟨c', u', hc', hu', hio⟩ := k11 c u hc hu
  obtain ⟨ζ0, hζ0, K⟩ := GlobalTheory.ConjGen.conj_gen GlobalTheory.chartIndependence_unconditional D G Pl0 T0' A' T R' F' κ v₀' O' ph hn k1 k2 k3 k4 k5
    j k6 k7 c' hc' u' hu' B hB k8 ω hω τ (k9 τ h1) h2
  obtain ⟨s, hs, -⟩ := K ψ ψ' t t' hψ hψ' hQ hQ' ht ht' h3
  have hξ : IsRoot1 ((R'.xi t' s : Circle) : ℂ) := by
    rw [ht'.1, MonoidHom.mul_apply, Circle.coe_mul]
    exact root_mul (hδ s) (hr s)
  refine ⟨_, root_mul hζ0 hξ, k10 _ _ _ _ ?_⟩
  rw [← hio, ← hio]
  exact hs h hh x x' hx

theorem smul_apply_of {M N : Type} [AddCommGroup M] [Module ℂ M] [AddCommGroup N] [Module ℂ N] (L : M →ₗ[ℂ] N) {ν a b : ℂ} {P Q : M}
    (h : ν • P = (a * b) • Q) : ν • L P = a • b • L Q := by
  rw [← map_smul, h, map_smul, mul_smul]

theorem rescale {X : Type} (τ : ℂ ≃+* ℂ) {ξ ζ : ℂ} (hξ : ξ ≠ 0) {Φ Φ' Ψ Ψ' : X → ℂ} (h : Ψ = ξ • Φ) (h' : Ψ' = ξ • Φ') {n : ℕ}
    {b : Fin n → ℂ} {f : Fin n → X → ℂ} (e1 : Φ = ∑ l, b l • f l) (e2 : ∑ l, τ (b l) • f l = fun x => ζ⁻¹ * Φ' x) :
    Ψ = ∑ l, (ξ * b l) • f l ∧ ∑ l, τ (ξ * b l) • f l = (τ ξ * ζ⁻¹ * ξ⁻¹) • Ψ' := by
  constructor
  · rw [h, e1, Finset.smul_sum]
    simp only [smul_smul]
  · have e3 : ∑ l, τ (ξ * b l) • f l = τ ξ • ∑ l, τ (b l) • f l := by
      simp only [map_mul, Finset.smul_sum, smul_smul]
    rw [e3, e2, h', smul_smul, inv_mul_cancel_right₀ hξ, mul_smul]
    rfl

end GlobalTheory.BigOn.Exp.TwConj
