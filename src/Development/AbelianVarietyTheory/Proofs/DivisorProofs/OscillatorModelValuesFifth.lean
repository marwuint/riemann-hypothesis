import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DictionaryComponentFrameMarkingUniformisation
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelFormCompatBaseEmbedding
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLatOfInt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HxOfIsONFr
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CastFrMemDom
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.AnalyticFibreUnitFrameUniformisation
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsLetterRowWeightDictionary
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ExistsSabMapOfIsAH
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.ClassSumValuesUnitOfClassSumValues
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.WeightZeroSectionValueConjPoint
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicUnitaryLatticeRationalTranslateInvariance
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAlgebraMapOfSigRFixed

open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.AdTh.CoverVal

theorem perFr_cast {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {X' X : Data E r} (h : SameSp X' X)
    (x : Frame X'.Ψ r) (v : Fin r → E) (τ : E →+* ℂ) (i : ℕ) :
    perFr X' x v τ i = perFr X (castFr h.psi x) v τ i := by
  obtain ⟨h1, h2, h3, -, -⟩ := h
  cases X
  cases X'
  dsimp only at h1 h2 h3
  subst h1 h2 h3
  rfl

theorem sameSp_of {D : D7} {W : HSp D} {r : ℕ} {hr : W.rank = r} {X' X : Data D.host.E r} (h' : IsMod W hr X')
    (h : IsMod W hr X) (hp : X'.p0 = X.p0) : SameSp X' X :=
  ⟨Finset.ext fun τ => (h'.psi τ).trans (h.psi τ).symm, h'.model.1.trans h.model.1.symm, hp,
    h'.model.2.trans h.model.2.symm, h'.kap.trans h.kap.symm⟩

theorem realM_mul {D : D7} {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (γ k : GA D W)
    (δ : Matrix (Fin W.rank) (Fin W.rank) D.host.E)
    (hδ : ∀ (τ : D.host.E →+* ℂ) th, IsInfEmb τ th → archM W th γ = δ.map τ) (τ : D.host.E →+* ℂ)
    (hτ : ∃ ρ, τ = tauE D ρ) :
    realM θ (Formalism.L2.Theta.mt W (γ * k)) τ = δ.map τ * realM θ (Formalism.L2.Theta.mt W k) τ := by
  have h1 := hδ τ (θ hτ.choose) (by have h := hθ hτ.choose; rwa [← hτ.choose_spec] at h)
  rw [realM, realM, dif_pos hτ, dif_pos hτ, ← h1]
  change archM W _ (γ * k) = _ * archM W _ k
  rw [archM, archM, archM, map_mul, Units.val_mul, Matrix.map_mul]

open CategoryTheory MonObj in

theorem marked_congr {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} [Algebra c.F ℂ] {r g : ℕ} {X : Data E r}
    {bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ} {idx : Fin g ≃ X.Ψ × Fin r} {e : Fin g ≃ Lt1 Dw} {x : Frame X.Ψ r}
    {L : Lt E r} {y : FrPt Xo c ℂ} (A : AnFib X bas idx e x L y) {mk mk' : Dw.La →ₗ[𝓞 E] (Fin r → E)}
    (h : A.Marked mk) (hc : ∀ a ∈ Mfr l • (⊤ : Submodule (𝓞 E) Dw.La), ∃ u ∈ L, mk' a = mk a + l.M • u) :
    A.Marked mk' := by
  intro a ha
  obtain ⟨u, hu, e'⟩ := hc a ha
  have hM : (l.M : E) ≠ 0 := by have := l.three_le; exact_mod_cast (by omega : l.M ≠ 0)
  have hadd : ∀ u v, pv X idx x (u + v) = pv X idx x u + pv X idx x v := fun u v => by
    unfold pv; rw [per_add]; rfl
  rw [h a ha, e', smul_add, ← Nat.cast_smul_eq_nsmul E, inv_smul_smul₀ hM, hadd, A.ex_add,
    (A.ex_ker _).2 ⟨u, hu, rfl⟩, _root_.mul_one]

theorem move_congr {A : Type} [CommRing A] {n N : ℕ} (p q : Matrix (Fin n) (Fin n) A) {x x' b w w' : Fin n → A}
    (h : x - q *ᵥ b = N • w) (h' : x' - p *ᵥ (q *ᵥ b) = N • w') : p *ᵥ x - x' = N • (p *ᵥ w - w') := by
  rw [smul_sub, ← h', ← Matrix.mulVec_smul, ← h, Matrix.mulVec_sub, sub_sub_sub_cancel_right]

theorem point_eq {D : D7} {H : Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Geo.Tor.Level H} {Xo : Moduli Dw l}
    {c : Coeff l} {σ : c.F →+* ℂ} {r : ℕ} (U : Formalism.L2.PjFree.Unf Xo c σ r) (hσ : GoodEmb c σ)
    (hU : Formalism.L2.PjFree.IsUnf U) (h1 : 1 ≤ r) (hA : l.A = 1) {θ : InfFam D} (hθ : IsInfFam θ) (W : HSp D) (hr : W.rank = r)
    (ι : Dw.La →ₗ[𝓞 D.host.E] (Fin W.rank → D.host.E)) (x₀ : (D.host.E →+* ℂ) → Matrix (Fin r) (Fin r) ℂ)
    (Wt : UW U) (j : U.Comp) (x' : Frame (U.X j).Ψ r) (γ k : GA D W) (hγ : γ ∈ GQ W) (hm' : IsMod W hr (U.X j))
    (hL' : latR hr (latG W (γ * k)) = (U.X j).Λ) (hx' : x' = frMove θ W hr (U.X j) (γ * k) fun τ => x₀ τ.1)
    (hon : IsONFr (U.X j) x') (hk' : MarkAd l W hr ι (γ * k) (Wt.mark j))
    (X : Data D.host.E r) (g : ℕ) (bas : (Fin g ⊕ Fin g → ℤ) ≃ₗ[ℤ] X.Λ) (idx : Fin g ≃ X.Ψ × Fin r) (e : Fin g ≃ Lt1 Dw)
    (mk : Dw.La →ₗ[𝓞 D.host.E] (Fin r → D.host.E)) (hm : IsMod W hr X) (hp : X.p0 = Dw.q) (hs : IsSympl X bas)
    (hi : IdxIs c σ X idx e) (hL : latR hr (latG W k) = X.Λ) (hmk : IsMark l X.Λ mk) (hk : MarkAd l W hr ι k mk) :
    letI : Algebra c.F ℂ := σ.toAlgebra
    ∀ (y : FrPt Xo c ℂ) (A : AnFib X bas idx e (frMove θ W hr X k fun τ => x₀ τ.1) X.Λ y), A.Marked mk →
      ∃ h : x' ∈ (U.X j).dom, y.x = (U.un j ⟨x', h⟩).x := by
  let _ : Algebra c.F ℂ := σ.toAlgebra
  intro y A hA'
  subst hr
  obtain rfl : g = Wt.g := Fin.equiv_iff_eq.1 ⟨e.trans Wt.e.symm⟩
  obtain ⟨π, rfl⟩ : ∃ π : Equiv.Perm (Fin Wt.g), e = π.trans Wt.e :=
    ⟨e.trans Wt.e.symm, Equiv.ext fun a => (Wt.e.apply_symm_apply _).symm⟩
  obtain ⟨idx, rfl⟩ : ∃ idx' : Fin Wt.g ≃ X.Ψ × Fin W.rank, idx = π.trans idx' :=
    ⟨π.symm.trans idx, Equiv.ext fun a => congrArg idx (π.symm_apply_apply a).symm⟩
  have hsp : SameSp (U.X j) X := sameSp_of hm' hm ((hU.2.1 j).1.trans hp.symm)
  obtain ⟨-, hsd, -⟩ := uw_lattice _ H Dw l Xo c σ _ U hσ hU h1 Wt j
  obtain ⟨Dc, hDc, -⟩ := exists_dic _ H Dw l c σ _ Wt.g 0 (U.X j) 0 Wt.e hσ hU.1 (hU.2.1 j).1 (hU.2.1 j).2 hsd
    ⟨fun _ => antitone_const, Even.zero⟩
  have hper := Dc.per_eq
  have hty := Dc.ty_eq
  rw [hDc] at hper hty
  obtain ⟨hd', hu', -⟩ := hx_of_isONFr _ _ _ 0 (U.X j) Dc.bas Dc.idx Dc.sympl Even.zero x' hon
  obtain ⟨A', hA'', -⟩ := uw_anFib _ H Dw l Xo c σ _ U hσ hU h1 Wt j Dc.bas Dc.idx Dc.sympl hper hty ⟨x', hd'⟩ hu'
  obtain ⟨δ, hδu, hδf, hδa⟩ := GlobalTheory.MarkCoset.rational_matrix W γ hγ
  have hri : ∀ v, δ.1 *ᵥ ((δ⁻¹).1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
  have hli : ∀ v, (δ⁻¹).1 *ᵥ (δ.1 *ᵥ v) = v :=
    fun v => by rw [Matrix.mulVec_mulVec, Units.inv_mul, Matrix.one_mulVec]
  have hG : X.Gm = -W.gram.transpose := hm.model.1
  have hun : IsUn X δ⁻¹ := fun u v => by rw [hG, ← hδu, hri, hri]
  have hR : ∀ L : Lt D.host.E W.rank, latR rfl L = L := fun L => Submodule.map_id L
  rw [hR] at hL hL'
  have hmem : ∀ v, v ∈ X.Λ ↔ δ.1 *ᵥ v ∈ (U.X j).Λ := fun v => by
    rw [← hL, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, GlobalTheory.Member.LatMove.mem_lat_iff,
      GlobalTheory.Member.LatMove.move_iff W γ k, hδf]
  obtain ⟨hd, -, hsd', A'', -, -, hM⟩ := anFib_move _ H Dw l Xo c _ _ (U.X j) X hsp Dc.bas Dc.idx bas idx Wt.e x' _ _ A' δ⁻¹
    Dc.sympl hs hd' hsd hun
    (fun v => funext fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hper x' v _).trans ((perFr_cast hsp _ _ _ _).trans (hi.1 _ v a).symm))
    (fun a => by
      obtain ⟨a, rfl⟩ := π.surjective a
      exact (hty _).trans (hi.2 a).symm)
  have hM' := hM _ hA''
  have e1 : mapL δ⁻¹ (U.X j).Λ = X.Λ := Submodule.ext fun v => by
    rw [Lev.mem_mapL, inv_inv, hmem]; rfl
  have e2 : lact δ⁻¹ (castFr hsp.psi x') = frMove θ W rfl X k fun τ => x₀ τ.1 := by
    funext τ
    rw [hx']
    change (δ⁻¹).1.map τ.1 * (realM θ (Formalism.L2.Theta.mt W (γ * k)) τ.1 * x₀ τ.1) =
      realM θ (Formalism.L2.Theta.mt W k) τ.1 * x₀ τ.1
    rw [realM_mul hθ W γ k δ.1 hδa τ.1 ((hm.psi _).1 τ.2), ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.map_mul,
      Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  revert A'' hd hsd'
  rw [e1, e2]
  intro hd hsd' A'' _ hM'
  refine ⟨hd', anFib_point_eq _ H Dw l Xo c hA _ _ X bas idx Wt.e _ _ _ y A'' (Cmp.anFibRen π A) hs hd hsd' mk hmk
    (marked_congr A'' hM' fun a ha => ?_) hA'⟩
  obtain ⟨w, hw, ew⟩ := hk a ha
  obtain ⟨w', hw', ew'⟩ := hk' a ha
  have hM0 : l.M ≠ 0 := by have := l.three_le; omega
  obtain ⟨u, hu, eu⟩ := GlobalTheory.MarkCoset.finVec_div W l.M hM0 (δ.1 *ᵥ mk a - Wt.mark j a) ((finHom W γ).1 *ᵥ w - w') (by
    have e3 : finVec W (δ.1 *ᵥ mk a - Wt.mark j a) = finVec W (δ.1 *ᵥ mk a) - finVec W (Wt.mark j a) :=
      funext fun i => TensorProduct.tmul_sub _ _ _
    rw [e3, ← hδf]
    exact move_congr _ _ ew (GlobalTheory.Member.LatMove.fin_mul W γ k _ ▸ ew'))
  refine ⟨(δ⁻¹).1 *ᵥ u, ?_, ?_⟩
  · rw [hmem, hri, ← hL', GlobalTheory.Member.LatMove.mem_lat_iff, hu]
    exact sub_mem (GlobalTheory.Member.LatMove.move_mem W γ k w hw) hw'
  · rw [← Matrix.mulVec_smul, ← eu, Matrix.mulVec_sub, hli]
    exact (add_sub_cancel _ _).symm

theorem evR_eq_of_point {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Geo.Tor.Host E} {Dw : Datum H}
    {l : Geo.Tor.Level H} {Xo : Moduli Dw l} {c : Coeff l} (σ : c.F →+* ℂ) {f : Rul Xo c} (hf : f ∈ sec Xo c 0 0)
    (y y' : FrPt Xo c (CAt σ)) (h : y'.x = y.x) : toC (evR Xo c f y') = toC (evR Xo c f y) :=
  GlobalTheory.WeightZeroValue.evR_conj E H Dw l Xo c σ (RingEquiv.refl ℂ) f hf y y'
    (h.trans ((CategoryTheory.Category.id_comp _).symm.trans
      (congrArg (CategoryTheory.CategoryStruct.comp · y.x) (AlgebraicGeometry.Spec.map_id _).symm)))

end GlobalTheory.AdTh.CoverVal
