import Formalism.LocalToGlobal.Columns.ChainLawXi
import Formalism.LocalToGlobal.Columns.ChainTw
import Formalism.LocalToGlobal.Columns.ChainTwZero
import Mathlib
import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
import Formalism.LocalToGlobal.KernelLattices.TopLawQ
import Formalism.LocalToGlobal.KernelLattices.ColInst
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
import Formalism.LocalToGlobal.Columns.ChainInstY
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.MemGoodPrimesOfNoExceptional

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section Stmt

variable {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S)
  (cst : LocCst X (rowSG Pr sel mu))

def TargetEquivarianceAtPrime (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∀ r' ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) hbe, ∀ c' ∈ GLint X.E (R.N (i + 1)) w.1,
    (∀ x, r' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (c' x)) →
    ∀ y : HomE X.E (R.N i) (R.N (i + 1)),
      rhoT Ch sel mu i w ((LinearEquiv.det c'⁻¹ : X.Eˣ) : X.E) * E1at Ch sel mu cst i w hal hbe (c'.toLinearMap ∘ₗ y) =
        chiInv Ch sel mu cst (i + 1) w hbe r' * E1at Ch sel mu cst i w hal hbe y

def TargetEquivarianceLargeDepths (i : ℕ) (w : rowSG Pr sel mu) (hal : AutY X R i) (hbe : AutY X R (i + 1)) : Prop :=
  ∃ A₀ B₀ : ℕ, ∀ A' B', A₀ ≤ A' → B₀ ≤ B' → TargetEquivarianceAtPrime Ch sel mu { cst with A := A', B := B' } i w hal hbe

end Stmt

section Res

variable {k : Type} [Field k] {n c : ℕ}

theorem clXQ_eq_inX {v : Fin (n + c) → k} (hv : v ∈ Loc.Ufl k n c 0) : v = Loc.inX k n c (twZrPr v) := by
  funext l
  unfold Loc.inX
  by_cases h : l.1 < n
  · simp only [LinearMap.pi_apply, dif_pos h, LinearMap.proj_apply]
    rfl
  · simp only [LinearMap.pi_apply, dif_neg h, LinearMap.zero_apply]
    exact hv l (by simpa using h)

theorem clXQ_res {r : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k)} (hr : r ∈ Loc.R1 k n c) :
    ∃ g : (Fin n → k) ≃ₗ[k] (Fin n → k), ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (g x) := by
  have h1 : ∀ x, r (Loc.inX k n c x) = Loc.inX k n c (twZrPr (r (Loc.inX k n c x))) :=
    fun x => clXQ_eq_inX (hr.1.1 0 _ (twZr_inX_mem_Ufl x 0))
  have h2 : ∀ x, r⁻¹ (Loc.inX k n c x) = Loc.inX k n c (twZrPr (r⁻¹ (Loc.inX k n c x))) :=
    fun x => clXQ_eq_inX (hr.2.1 0 _ (twZr_inX_mem_Ufl x 0))
  refine ⟨LinearEquiv.ofLinear (twZrPr ∘ₗ r.toLinearMap ∘ₗ Loc.inX k n c) (twZrPr ∘ₗ (r⁻¹).toLinearMap ∘ₗ Loc.inX k n c) ?_ ?_, h1⟩
  · refine LinearMap.ext fun x => ?_
    show twZrPr (r (Loc.inX k n c (twZrPr (r⁻¹ (Loc.inX k n c x))))) = x
    rw [← h2]
    show twZrPr (r (r.symm (Loc.inX k n c x))) = x
    rw [LinearEquiv.apply_symm_apply, twZrPr_inX]
  · refine LinearMap.ext fun x => ?_
    show twZrPr (r⁻¹ (Loc.inX k n c (twZrPr (r (Loc.inX k n c x))))) = x
    rw [← h1]
    show twZrPr (r.symm (r (Loc.inX k n c x))) = x
    rw [LinearEquiv.symm_apply_apply, twZrPr_inX]

end Res

section Chr

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ} {mu : Tup X.F X.E X.K S}
  {cst : LocCst X (rowSG Pr sel mu)}

theorem clXQ_rhoT_ne (i : ℕ) (w : rowSG Pr sel mu) {n : ℕ} {c : Sp X.E n ≃ₗ[X.E] Sp X.E n} (hc : c ∈ GLint X.E n w.1) :
    rhoT Ch sel mu i w ((LinearEquiv.det c : X.Eˣ) : X.E) ≠ 0 := by
  unfold rhoT
  exact clX_unitV_ne _ (isUnit_reduction_of_integralAt_inv (intAt_det c hc) (intAt_det_inv c hc) (Units.ne_zero _))

theorem clXQ_rhoT_mul (i : ℕ) (w : rowSG Pr sel mu) {n : ℕ} {c c' : Sp X.E n ≃ₗ[X.E] Sp X.E n} (hc' : c' ∈ GLint X.E n w.1) :
    rhoT Ch sel mu i w ((LinearEquiv.det (c * c') : X.Eˣ) : X.E) =
      rhoT Ch sel mu i w ((LinearEquiv.det c : X.Eˣ) : X.E) * rhoT Ch sel mu i w ((LinearEquiv.det c' : X.Eˣ) : X.E) := by
  unfold rhoT
  rw [map_mul, Units.val_mul]
  exact unitV_mul_unit _ (intAt_det c' hc') (intAt_det_inv c' hc') (Units.ne_zero _) _

theorem clXQ_chrOk {i : ℕ} {w : rowSG Pr sel mu} {hal : AutY X R i} {h : AutY X R (i + 1)}
    (hint : prCat (Pr := Pr) cst.sharp (i + 1) w.1 h ≤ GLint X.E (R.N (i + 1)) w.1)
    (hT : TargetEquivarianceLargeDepths Ch sel mu cst i w hal h) (hne : FiniteSumNonzeroLargeDepth Ch sel mu cst i w hal h) : TwChrOk Ch sel mu cst (i + 1) w h := by
  obtain ⟨A₀, B₀, hT⟩ := hT
  obtain ⟨A₁, B₁, hne⟩ := hne
  have T := hT (max A₀ A₁) (max B₀ B₁) (le_max_left _ _) (le_max_left _ _)
  obtain ⟨y₀, hy₀⟩ := Function.ne_iff.1 (hne (max A₀ A₁) (max B₀ B₁) (le_max_right _ _) (le_max_right _ _))
  have hres : ∀ r ∈ Loc.Cbe (Jat (Pr := Pr) cst.sharp (i + 1) w.1) h, ∃ c ∈ GLint X.E (R.N (i + 1)) w.1,
      ∀ x, r (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) (c x) := by
    intro r hr
    obtain ⟨c, hc⟩ := clXQ_res (Subgroup.mem_inf.1 hr).1
    exact ⟨c, hint ⟨r, hr, hc⟩, hc⟩
  refine ⟨fun r hr h0 => ?_, fun r hr r' hr' r'' hr'' hx => ?_⟩
  · obtain ⟨c, hc, hcx⟩ := hres r hr
    have e := T r hr c hc hcx ((c⁻¹).toLinearMap ∘ₗ y₀)
    have h0' : chiInv Ch sel mu { cst with A := max A₀ A₁, B := max B₀ B₁ } (i + 1) w h r = 0 := h0
    rw [h0', zero_mul] at e
    have e2 : c.toLinearMap ∘ₗ (c⁻¹).toLinearMap ∘ₗ y₀ = y₀ := by
      refine LinearMap.ext fun v => ?_
      show c (c.symm (y₀ v)) = y₀ v
      rw [LinearEquiv.apply_symm_apply]
    rw [e2] at e
    rcases mul_eq_zero.1 e with e | e
    · exact clXQ_rhoT_ne i w ((GLint X.E (R.N (i + 1)) w.1).inv_mem hc) e
    · exact hy₀ e
  · obtain ⟨c, hc, hcx⟩ := hres r hr
    obtain ⟨c', hc', hcx'⟩ := hres r' hr'
    have hcx'' : ∀ x, r'' (Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) x) = Loc.inX X.E (R.N (i + 1)) (cOf R (i + 1)) ((c * c') x) := by
      intro x
      rw [hx, hcx', hcx]
      rfl
    have e'' := T r'' hr'' (c * c') ((GLint X.E (R.N (i + 1)) w.1).mul_mem hc hc') hcx'' y₀
    have e := T r hr c hc hcx (c'.toLinearMap ∘ₗ y₀)
    have e' := T r' hr' c' hc' hcx' y₀
    have e3 : (c * c').toLinearMap ∘ₗ y₀ = c.toLinearMap ∘ₗ c'.toLinearMap ∘ₗ y₀ := rfl
    rw [e3, mul_inv_rev, clXQ_rhoT_mul i w ((GLint X.E (R.N (i + 1)) w.1).inv_mem hc), mul_assoc, e, ← mul_assoc,
      mul_comm (rhoT Ch sel mu i w _), mul_assoc, e', ← mul_assoc] at e''
    exact (mul_right_cancel₀ hy₀ e'').symm

end Chr

end Formalism.L2.Col
