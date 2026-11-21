import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerWindowSums
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.GaloisCohomology.LocalTateDualityK
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh

noncomputable section

namespace GlobalTheory.TorsionBoundCompare

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N TensorProduct

section Generic

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL]
    [CommRing O] [Algebra O LL] [TopologicalSpace LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {W : LocWach PD LL O v n} {RA RW : Type} [CommRing RA] [CommRing RW] [Algebra O RA]
    [Algebra O RW] {inclR : RA →ₐ[O] RW} {φR : RW →ₐ[O] RW} {gR : G → (RW →ₐ[O] RW)} {πA : RA}
    (E : EtTie W RA RW inclR φR gR πA)

theorem TWact_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (g : G) (r : RW) (y : TW RW T) :
    TWact f T g (r • y) = f r • TWact f T g y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWact, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem TWmap_smul (f : RW →ₐ[O] RW) (T : LocLat G Qp LL O) (r : RW) (y : TW RW T) :
    TWmap f T (r • y) = f r • TWmap f T y := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul a t => simp [TWmap, TensorProduct.smul_tmul']
  | add a b ha hb => simp [ha, hb]

theorem unit_cancel (hO : Function.Injective (algebraMap O LL)) :
    ∃ (e : W.DD W.one) (e₀ : ↥W.one.L.T), E.jD W.one e = (1 : RW) ⊗ₜ[O] e₀ ∧
      ∀ r r' : RW, r • ((1 : RW) ⊗ₜ[O] e₀) = r' • ((1 : RW) ⊗ₜ[O] e₀) → r = r' := by
  obtain ⟨e, e₀, h1, h2, -⟩ := E.one_e
  obtain ⟨x, hx, hT⟩ := W.one_line
  have h0 : (e₀ : W.one.V) ≠ 0 := by
    intro h
    have hm : (⟨x, by rw [hT]; exact Submodule.mem_span_singleton_self x⟩ : ↥W.one.L.T) ∈
        Submodule.span O {e₀} := by rw [h1]; trivial
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hm
    have := congrArg Subtype.val hc
    simp only [SetLike.val_smul, h, smul_zero] at this
    exact hx this.symm
  have hb : Function.Bijective (LinearMap.toSpanSingleton O _ e₀) := by
    refine ⟨(injective_iff_map_eq_zero _).mpr fun c hc => ?_, ?_⟩
    · have := congrArg Subtype.val hc
      simp only [LinearMap.toSpanSingleton_apply, SetLike.val_smul, ZeroMemClass.coe_zero] at this
      rw [← algebraMap_smul LL, smul_eq_zero] at this
      exact hO (by rw [this.resolve_right h0, map_zero])
    · rw [← LinearMap.range_eq_top, ← LinearMap.span_singleton_eq_range, h1]
  let lam := (LinearEquiv.ofBijective _ hb).symm
  have hl : lam e₀ = 1 := by
    rw [LinearEquiv.symm_apply_eq]; simp
  refine ⟨e, e₀, h2, fun r r' h => ?_⟩
  have := congrArg (fun y => TensorProduct.rid O RW (LinearMap.lTensor RW lam.toLinearMap y)) h
  simpa [TensorProduct.smul_tmul', hl] using this

theorem ioE_φ (hO : Function.Injective (algebraMap O LL)) (a : W.EE) :
    E.ioE (W.φE a) = φR (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h3 : TWmap φR W.one ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWmap]
  have := E.jD_φ W.one (a • e)
  rw [W.φD_smul, E.jD_smul, E.jD_smul, E.jD_φ, TWmap_smul, h1, h3] at this
  exact h2 _ _ this

theorem ioE_γ (hO : Function.Injective (algebraMap O LL)) (g : G) (a : W.EE) :
    E.ioE (W.γE (W.resΓ g) a) = gR g (E.ioE a) := by
  obtain ⟨e, e₀, h1, h2⟩ := unit_cancel E hO
  have h4 : W.one.actT g e₀ = e₀ := Subtype.ext (W.one_triv g _)
  have h3 : TWact (gR g) W.one g ((1 : RW) ⊗ₜ[O] e₀) = (1 : RW) ⊗ₜ[O] e₀ := by simp [TWact, h4]
  have := E.jD_act W.one g (a • e)
  rw [W.γD_smul, E.jD_smul, E.jD_smul, E.jD_act, TWact_smul, h1, h3] at this
  exact h2 _ _ this

def sc : LetA O n →ₐ[O] RW := inclR.comp E.io

theorem sc_φ (hO : Function.Injective (algebraMap O LL)) (a : LetA O n) :
    sc E (W.φA a) = φR (sc E a) := by
  have := ioE_φ E hO (algebraMap _ _ a)
  rwa [W.φE_ext, E.ioE_ext, E.ioE_ext] at this

def cst (c : ZMod n → O) : LetA O n := fun i => PowerSeries.C (c i)

theorem φA_cst (c : ZMod n → O) : W.φA (cst c) = cst fun i => c (i - 1) := by
  funext i
  exact W.φ₀.commutes (c (i - 1))

theorem iter_sc_cst (hO : Function.Injective (algebraMap O LL)) (c : ZMod n → O) (k : ℕ) :
    φR^[k] (sc E (cst c)) = sc E (cst fun i => c (i - k)) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih, ← sc_φ E hO, φA_cst]
    congr 2
    funext i
    congr 1
    push_cast
    ring

end Generic

section Comp

variable {Z O R R' : Type} [CommRing Z] [CommRing O] [CommRing R] [CommRing R'] [Algebra Z O]
  [Algebra Z R] [Algebra Z R']

def cf (lam : O →ₗ[Z] Z) : O ⊗[Z] R →ₗ[Z] R :=
  (TensorProduct.lid Z R).toLinearMap ∘ₗ lam.rTensor R

end Comp

section Situation

open GlobalTheory.IndefiniteRowSideFullHecke.SelmerFiniteUnramified

variable {l : ℕ} [Fact l.Prime]

theorem inclW_frob (a : Ainf l) : inclW l (WittVector.frobenius a) = frobW l (inclW l a) := by
  ext n
  change ((WittVector.map _ _ : WCb l)).coeff n = (WittVector.map (frobenius (Cb l) l) (inclW l a)).coeff n
  simp [inclW, WittVector.map_coeff, frobenius_def]

theorem tmul_iter (LL : FinExt l) (k : ℕ) (x : WCb l) :
    (φRW LL)^[k] ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] x) = (1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] (frobW l)^[k] x := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih]; rfl

variable {P : LocPrime l} {AI : LocAinf l P} {K : FinExt l} {s : ℕ} {LL : FinExt l}
  {W : LocWach (P.PD K) ↥LL.1 ↥(OL LL) (P.v LL) (Module.finrank ℚ_[l] ↥(K0 K))}
  (E : EtTie W (RA LL) (RW LL) (inclR LL) (φRW LL) (fun g : ↥(GK K) => AI.gRW LL (g : GQ l))
    ((1 : ↥(OL LL)) ⊗ₜ[ℤ_[l]] piS AI s))

theorem frob_teich (x : OCb l) :
    WittVector.frobenius (WittVector.teichmuller l x) = WittVector.teichmuller l (x ^ l) := by
  rw [WittVector.frobenius_eq_map_frobenius, WittVector.map_teichmuller, frobenius_def]

end Situation

end GlobalTheory.TorsionBoundCompare
