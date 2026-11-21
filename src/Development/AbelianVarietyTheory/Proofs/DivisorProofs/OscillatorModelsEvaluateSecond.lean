import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReadingsExistRow
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteGroupActsByLiftTranslationPrincipalType

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice MeasureTheory IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Pj Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.WeilGramSignature
open scoped TensorProduct InnerProductSpace
open GlobalTheory.GalLift
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.GalLift.BaseId

variable {D : D7}

section Row

open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem tie_baseChange {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host D.host.E} {Dw : Datum H} {l : Level H} {Xo : Moduli Dw l} {c c' : Coeff l}
    (hle : c.F ≤ c'.F) {r n : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r) (σ' : c'.F →+* ℂ) (V : HSp D)
    (dict : GA D V → Σ k, Frame ((U (σ'.comp (incF c c' hle))).X k).Ψ r) (mu : GA D V → ℂ) (xr : ℝ)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) {Γ : Type} [Group Γ]
    {act : Γ → Rul Xo c →ₗ[c.F] Rul Xo c} {act' : Γ → Rul Xo c' →ₗ[c'.F] Rul Xo c'}
    {Vs : Type} [AddCommGroup Vs] [Module c'.F Vs] {Tup : Type} {dδ : Tup → DeltaDat Xo c' n}
    {Cl' : Tup → Type} [∀ t, Fintype (Cl' t)]
    {w : ∀ t, Cl' t → (Fin n → LevQ Dw (dδ t).l₂) → c'.F} {La : ∀ t, Cl' t → GenLat D.host.E n} {Nc : ∀ t, Cl' t → ℕ}
    {gam : ∀ t, Cl' t → ℕ} {vol : Tup → c'.F} {ep : ∀ t, Cl' t → c'.F} {io : Vs →ₗ[c'.F] MvPolynomial (LtN Dw n) c'.F}
    {thAd : ∀ t, (Cl' t → Vs) → (AutQ V → ℂ)} {Pl : ∀ t, (Cl' t → Vs) → Prop} {LL : IntermediateField ℚ ℂ}
    {cc : (U (σ'.comp (incF c c' hle))).Comp → ℂ} {ph : ℂ}
    (htie : OneMapTieC hle LL U σ' V dict mu xr a act act' dδ Cl' w La Nc gam vol ep io thAd Pl cc ph) (t : Tup) :
    ∃ z ∈ Subgroup.center Γ, ∃ ze ∈ LL, (∃ m : ℕ, 0 < m ∧ ze ^ m = 1) ∧ ∀ x : Cl' t → Vs, Pl t x →
      ∃ (f' : Rul Xo c') (m : ℕ) (as : Fin m → c'.F) (fs : Fin m → Rul Xo c), f' ∈ sec Xo c' a n ∧
        IsThClsD Xo c' (dδ t) (w t) (La t) (Nc t) (gam t) (vol t) (ep t) io x f' ∧ (∀ k, fs k ∈ cusp Xo c U a n) ∧
        IsBC hle f' as fs ∧ ∀ q : AutQ V, ph * thAd t x q = ∑ k, ze * σ' (as k) * ((lieFac Dw xr a : ℂ) *
          adel V dict (muPin V dict mu cc) (rdU (U (σ'.comp (incF c c' hle))) (act z (fs k))) q.out) := by
  obtain ⟨-, hC, hA, -, -, z, hz, hrow⟩ := htie
  obtain ⟨ze, hze, hroot, hrow⟩ := hrow t
  refine ⟨z, hz, ze, hze, hroot, fun x hx => ?_⟩
  obtain ⟨⟨f', hf', hcl⟩, hall⟩ := hrow x hx
  have hf's := cusp_le_sec _ _ _ _ _ hf'
  obtain ⟨m, as, fs, hfs, hBC⟩ := hC a n f' hf'
  have hBCz := hA a n z m as fs f' hf's (fun k => cusp_le_sec _ _ _ _ _ (hfs k)) hBC
  refine ⟨f', m, as, fs, hf's, hcl, hfs, hBC, fun q => ?_⟩
  have h1 := hall f' hf's hcl q
  have h2 := GlobalTheory.PhaseRational.rdU_of_isBC hle U σ' hBCz (dict q.out).1 (dict q.out).2
  have h3 : jFn V σ' (rdU (unfBC hle U σ')) dict mu (act' z f') q = mu q.out * ∑ k, σ' (as k) *
      rdU (U (σ'.comp (incF c c' hle))) (act z (fs k)) (dict q.out).1 (dict q.out).2 :=
    congrArg (mu q.out * ·) h2
  rw [h1, h3, Finset.mul_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [adel_muPin]
  change ze * cc (dict q.out).1 * _ * _ = _
  ring

end Row

theorem phiC_congr (T : CoreJ D) {j : ℕ} {σ σ' : T.Q.c.F →+* ℂ} (e : σ = σ') {W : HSp D} (hV : T.V j σ = W)
    (hV' : T.V j σ' = W) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (f : T.R j) : phiC T hV a f = phiC T hV' a f := by
  subst e
  rfl

theorem proj_model {V : HSp D} {S : D.what₂.Tau → SPar} (M : DSModel V S) {X G : Type} [AddCommGroup X] [Module ℂ X] [Fintype G]
    (e : X →ₗ[ℂ] MMap M) (he : Function.Injective e) (L : G → (GA D V → ℂ) →ₗ[ℂ] (GA D V → ℂ)) (c : G → ℂ)
    (ρ : G → X →ₗ[ℂ] X) (hρ : ∀ g x, e (ρ g x) = postOn M (L g) (e x)) (ph : ℂ) (y y' w : X)
    (hy : e y' = postOn M (∑ g, c g • L g) (e y)) (hw : ph • y = w) : ph • y' = ∑ g, c g • ρ g w := by
  have h1 : y' = ∑ g, c g • ρ g y := by
    apply he
    rw [hy, map_sum]
    simp only [map_smul, hρ]
    ext v x
    simp [postOn, LinearMap.sum_apply, Finset.sum_apply]
  rw [h1, ← hw, Finset.smul_sum]
  exact Finset.sum_congr rfl fun g _ => by rw [map_smul, smul_comm]

theorem eq_of_reps {V : HSp D} {S : D.what₂.Tau → SPar} {θ} {M : DSModel V S} {J : Set (GA D V)} {χ : GA D V → ℂ}
    {X : Type} [AddCommGroup X] [Module ℂ X] (e : X →ₗ[ℂ] MMap M) (hr : LinearMap.range e = Mult.Mult θ M J χ) (v : M.Vec)
    (hinj : Function.Injective fun x => e x v) (ph : ℂ) (y : X) {n : ℕ} (b : Fin n → ℂ) (u : Fin n → X)
    (h : ∀ q : AutQ V, ph * e y v q.out = ∑ k, b k * e (u k) v q.out) : ph • y = ∑ k, b k • u k := by
  apply hinj
  funext g
  refine GlobalTheory.PhaseRational.eq_of_out
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v)
    (GlobalTheory.PhaseRational.mult_leftInv (hr.le (LinearMap.mem_range_self e _)) v) (fun q => ?_) g
  simpa [map_sum, Finset.sum_apply] using h q

end GlobalTheory.GalLift.BaseId

end
