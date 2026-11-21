import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GenReads
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.HolomorphicFamilies.CmHostUnitAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationSplitSupportProjectsVacuum
import Development.AbelianVarietyTheory.Definitions.Divisors.PerCEmb
import Development.AbelianVarietyTheory.Definitions.Divisors.MarkAd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LatticeIsometrySignSecond
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OrthonormalFrameReadingEqConjugateDatumThetaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPureTensorAtOriginEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThPBilinearHeis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxTranslateExponent
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaReadingLinearInjectiveAtOrthonormalFrame
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenMapTranspose
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSelfDualCHLat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinTensAlgebraMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PolyDerivCompNeg
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaPairCharactersAtLevel
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.PureTensorLIntertwine
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.ShortSeries

section Classical

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r g n : ℕ} {X : Data E r}
  {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ}

theorem heisG_smul (y : Matrix (Fin n) (Fin r) E) (c : ℂ) (φ : TF n g) :
    heisG X bas y (c • φ) = c • heisG X bas y φ := by
  funext x
  simp only [heisG, heisS, Pi.smul_apply, smul_eq_mul, mul_assoc]

theorem projA_smul (w : E) (A : AddSubgroup (Matrix (Fin n) (Fin r) E)) (a : ℂ) (φ : TF n g) :
    projA X bas w A (a • φ) = a • projA X bas w A φ := by
  by_cases ha : a = 0
  · subst ha
    have h0 : ∀ y : Matrix (Fin n) (Fin r) E, heisG X bas y (0 : TF n g) = 0 := fun y => by
      have := heisG_smul (X := X) (bas := bas) y 0 (0 : TF n g)
      rwa [zero_smul, zero_smul] at this
    rw [zero_smul, zero_smul, projA, finsum_mem_eq_zero_of_forall_eq_zero, smul_zero]
    rintro _ ⟨y, -, rfl⟩
    simp only [h0, smul_zero]
  have hi : Function.Injective fun ψ : TF n g => a • ψ := smul_right_injective _ ha
  have e : (fun y => epsW X w y • heisG X bas y (a • φ)) '' A =
      (fun ψ : TF n g => a • ψ) '' ((fun y => epsW X w y • heisG X bas y φ) '' A) := by
    rw [Set.image_image]
    congr 1
    funext y
    rw [heisG_smul, smul_comm]
  unfold projA
  rw [e, Set.ncard_image_of_injective _ hi, finsum_mem_image hi.injOn, smul_comm a]
  congr 1
  rw [smul_finsum]
  simp only [smul_finsum]

theorem theta_smul₂ (idx : Fin g ≃ X.Ψ × Fin r) (hs : IsSympl X bas) (hn : Even n) {q0 : ℕ} (hq : X.p0 + q0 = r)
    {x : Frame X.Ψ r} (hx : x ∈ X.dom) (c : ℂ) (φ : TF n g) (h : GlobalTheory.SW.IsSB (c • φ))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin n)) : thP X hq bas idx (c • φ) P x = c * thP X hq bas idx φ P x := by
  have key : ∀ (a : ℂ) (ψ : TF n g), GlobalTheory.SW.IsSB ψ → thP X hq bas idx (a • ψ) P x = a * thP X hq bas idx ψ P x := by
    intro a ψ hψ
    have := (theta_bilinear_heisenberg E r g n X bas idx hs hn q0 hq x hx ψ hψ P).1 ψ hψ a 0
    rwa [zero_smul, add_zero, zero_mul, add_zero] at this
  by_cases hc : c = 0
  · have := key 0 _ h
    rw [zero_smul] at this
    rw [hc, zero_smul, this, zero_mul, zero_mul]
  · refine key c φ ?_
    have := (isSB_algebra_haar_linear ℚ _ _ _ _ h h).2.1 c⁻¹
    rwa [inv_smul_smul₀ hc] at this

theorem finite_levQ {H : Geo.Tor.Host E} (Dw : Datum H) (l : Geo.Tor.Level H) : Finite (LevQ Dw l) := by
  have hM : l.Mb ≠ ⊥ := by
    intro h
    have h₁ := l.prod
    rw [h, Ideal.bot_mul, eq_comm, Ideal.span_singleton_eq_bot] at h₁
    have h₂ : l.M = 0 := by exact_mod_cast h₁
    have := l.three_le
    omega
  have := l.Mb.finiteQuotientOfFreeOfNeBot hM
  have := Dw.fin
  exact Submodule.finite_quotient_smul l.Mb (N := (⊤ : Submodule (𝓞 E) Dw.La)) Module.Finite.fg_top

theorem cmHost_idempotent_trace_eq_one (H : Geo.Tor.Host E) : (H.w0 : E) + cc (H.w0 : E) = 1 := by
  rw [cc, ← H.bar_eq]
  exact_mod_cast congrArg (fun t : 𝓞 E => (t : E)) (PullbackSections.CVA.cmHostUnit_add_conj_eq_one H)

end Classical

variable {D : D7} {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {V W : HSp D} {r g : ℕ}

theorem isInvOf_move (hr : W.rank = r) (X : Data D.host.E r) {x : Frame X.Ψ r}
    {s : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (k : GA D W) :
    IsInvOf W hr X (frMove θ W hr X k x)
      fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹) := by
  subst hr
  intro ρ τ hτ
  have h := hs ρ τ hτ
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  change s ρ * mat x τ = _ at h
  change (compAt θ ρ (Formalism.L2.Theta.mt W k) * s ρ * compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)) * _ = _
  rw [e, Matrix.mul_assoc, ← Matrix.mul_assoc (compAt θ ρ (Formalism.L2.Theta.mt W k⁻¹)),
    GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.one_mul, Matrix.mul_assoc, h, Matrix.mul_neg, Matrix.mul_assoc]

theorem isBasOf_move (hr : W.rank = r) (X : Data D.host.E r) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r}
    {B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hB : IsBasOf W hr X hq x B) (k : GA D W) :
    IsBasOf W hr X hq (frMove θ W hr X k x) fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ := by
  subst hr
  intro ρ τ hτ j i a hi
  have e : mat (frMove θ W rfl X k x) τ = compAt θ ρ (Formalism.L2.Theta.mt W k) * mat x τ := by
    rw [← RealCoord.realM_tauE, ← hτ]
    rfl
  refine Eq.trans ?_ (congrFun (congrFun e a) (rowIdx hq j)).symm
  simp only [Matrix.mul_apply]
  exact Finset.sum_congr rfl fun b _ => congrArg _ (hB ρ τ hτ j i b hi)

theorem isONFr_move (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) (k : GA D W) : IsONFr X (frMove θ W hr X k x) := by
  subst hr
  obtain ⟨X', m, hq', hq, bas', idx', hs, -, -, -, -, -, -, hfr⟩ :=
    GlobalTheory.T.orthonormal_frame_reading_eq_conjugate_datum_theta D ψ θ V W g X bas idx hψ hθ he hV hM hS
  obtain ⟨⟨B, hB⟩, hBx⟩ := hfr x hx
  obtain ⟨-, -, -, -, -, -, -, hmv, -⟩ := hBx B hB
  exact (hmv k).1

theorem reads_sum (hψ : IsStdChar D ψ (-1)) (hθ : IsInfFam θ) (hV : V.gram = 1) (he : Even V.rank) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {x : Frame X.Ψ r} (hx : IsONFr X x) {f : WO V W → ℂ} {φ : TF V.rank g}
    (hf : IsThetaFunO ψ V W f) (hR : Reads θ V W hr X bas idx f φ x) {Q : Type} (c : Q → ℂ)
    (γ : Q → Matrix (Fin W.rank) (Fin V.rank) D.host.E) (u : Q → WO V W) (hu : ∀ q, IsFinOf V W (γ q) (u q))
    (s : Finset Q) :
    IsThetaFunO ψ V W (∑ q ∈ s, c q • heisO ψ V W (u q) f) ∧
      Reads θ V W hr X bas idx (∑ q ∈ s, c q • heisO ψ V W (u q) f)
        (∑ q ∈ s, c q • heisG X bas (-(colsR hr (γ q))) φ) x := by
  have hlin := reads_linear_injective D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx
  induction s using Finset.induction_on with
  | empty =>
    have := (hlin _ _ _ _ hR hR).1 0 0
    simp only [zero_smul, add_zero] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_zero, this⟩
  | insert q s hq ih =>
    rw [Finset.sum_insert hq, Finset.sum_insert hq]
    have h1 := reads_heisO_finOf D ψ θ V W r g hr X bas idx hψ hθ hV he hM hS x hx f φ hf hR _ _ (hu q)
    have := (hlin _ _ _ _ h1 ih.2).1 (c q) 1
    rw [one_smul, one_smul] at this
    exact ⟨GlobalTheory.OrientedHeis.theta_add (GlobalTheory.OrientedHeis.theta_smul _ (GlobalTheory.FinTranslate.isThetaFunO_heisO hψ.1.1 hψ.1.2.1 hf (hu q).1)) ih.1, this⟩

theorem kernel_of_reads {χV χW : (AE D)ˣ →* Circle} {om : GA D V × GA D W →* Module.End ℂ (WO V W → ℂ)}
    (hP : IsPair ψ θ V W χV χW om) (hr : W.rank = r)
    (X : Data D.host.E r) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (hM : IsMod W hr X)
    (hS : IsSympl X bas) {q0 : ℕ} (hq : X.p0 + q0 = r) {x : Frame X.Ψ r} (hx : IsONFr X x)
    {s B : D.what₂.Tau → Matrix (Fin W.rank) (Fin W.rank) ℂ} (hs : IsInvOf W hr X x s) (hB : IsBasOf W hr X hq x B)
    {vr : Harm.Var X.Ψ q0 X.p0 (Fin V.rank) ≃ FVar D W.rank V.rank} (hvr : IsVarOf V W X q0 vr)
    {h : GA D V} (hh : h ∈ GfC V) (k : GA D W) {f : WO V W → ℂ} (hf : IsThetaFunO ψ V W f) {φ : TF V.rank g}
    (hR : Reads θ V W hr X bas idx (om (h, k) f) φ (frMove θ W hr X k x))
    (P : Harm.Poly ℂ X.Ψ q0 X.p0 (Fin V.rank)) (d : ℕ) (hd : P.IsHomogeneous d) :
    thetaKO om h k (pureTensorO ψ θ V W (fun _ => 1) s (fun _ => 1) B f (MvPolynomial.rename vr P)) =
      ((Real.sqrt (2 * Real.pi * xiR D) : ℝ) : ℂ)⁻¹ ^ d * thP X hq bas idx φ P (frMove θ W hr X k x) := by
  have h1 := (GlobalTheory.OrientedHeis.om_pureTensorO D ψ θ V W χV χW om hP.weil hP.inf (fun _ => 1) (fun _ => 1) (fun _ => 1)
    (fun _ => 1) s (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * s τ * compAt θ τ (Formalism.L2.Theta.mt W k⁻¹)) B
    (fun τ => compAt θ τ (Formalism.L2.Theta.mt W k) * B τ) h k
    (fun τ => by rw [Matrix.one_mul, Matrix.mul_one])
    (fun τ => by rw [Matrix.mul_assoc, GlobalTheory.WeilVacMove.compAt_mt_inv_mul, Matrix.mul_one])
    (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ V hh, Matrix.mul_one]) (fun _ => rfl) f hf
    (MvPolynomial.rename vr P)).2
  rw [thetaKO, h1]
  exact GlobalTheory.T.fock_pure_tensor_at_origin_eq_theta_series D ψ θ V W r g hr X bas idx hP.weil.std hP.inf hP.std hP.even hM hS q0 hq _ _ _ vr
    (isONFr_move hP.weil.std hP.inf hP.std hP.even hr X bas idx hM hS hx k) (isInvOf_move hr X hs k)
    (isBasOf_move hr X hq hB k) hvr _ φ (hP.weil.om_pres _ _ hf) hR P d hd

theorem exists_finOf (V W : HSp D) (hr : W.rank = r) (y : Matrix (Fin V.rank) (Fin r) D.host.E) :
    ∃ p : Matrix (Fin W.rank) (Fin V.rank) D.host.E × WO V W, colsR hr p.1 = y ∧ IsFinOf V W p.1 p.2 := by
  subst hr
  exact ⟨(yᵀ, GlobalTheory.LatVac.finTens 1 yᵀ), rfl, (GlobalTheory.VacSign.isFinOf_iff _ _).2 rfl⟩

end GlobalTheory.AdTh.ShortSeries
