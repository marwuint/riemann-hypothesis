import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.ExistsIdealDenominator
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood
import Formalism.SharpRestriction.LevelLetterCocycles.LocsCoverTw
import Formalism.SharpRestriction.Divisibility.CartierLocalBounds
import Formalism.SharpRestriction.Divisibility.LiftErrorLocal

noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions
open scoped TensorProduct

namespace Formalism.MainNotions.PDVN

variable (D : Formalism.BasicNotions.D7)

structure Loc where

  cE : ∀ i, D.ntw.abelian₂ i → ℕ

  kap : ∀ i, D.ntw.abelian₂ i → ℕ

  ffP : Finset ℕ

  a0 : ℕ → ℕ
  a0_mem_one_two : ∀ p ∈ ffP, a0 p = 1 ∨ a0 p = 2

  g_mem : ∀ k, D.host.g k ∈ ffP
  pde_mem : D.host.pde ∈ ffP ∧ D.host.pde' ∈ ffP

variable {D} in

def Loc.wt (X : Loc D) (i : D.ntw.Tw) (lam : D.ntw.abelian₂ i) : ℝ :=
  (X.kap i lam : ℝ) + (D.ntw.s2 i lam : ℝ) * (D.R.f : ℝ)

def oW (l : ℕ) [Fact l.Prime] (E : Type) [Field E] [NumberField E] (Λ : Type) [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (a : 𝓞 E) : (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) :=
  LinearMap.baseChange ℂ_[l] (DistribSMul.toAddMonoidHom Λ a).toIntLinearMap

structure PtTie {l : ℕ} [Fact l.Prime] (E : Type) [Field E] [NumberField E] {Λ σ : Type} [AddCommGroup Λ]
    [Module (𝓞 E) Λ] (Y : Formalism.MainNotions.ExistsIdealDenominator.PtGeo l Λ σ) {Bx Ex : Type} (lx : σ → Bx) (le : σ → Ex)
    (slx : Bx → (𝓞 E →+* ℂ_[l])) where

  HA : Type
  [acgHA : AddCommGroup HA]
  [modHA : Module ℂ_[l] HA]
  LA : Type
  [acgLA : AddCommGroup LA]
  [modLA : Module ℂ_[l] LA]
  pr : HA →ₗ[ℂ_[l]] LA
  pr_surj : Function.Surjective pr

  oH : 𝓞 E →+* Module.End ℂ_[l] HA
  oL : 𝓞 E →+* Module.End ℂ_[l] LA
  pr_o : ∀ a h, pr (oH a h) = oL a (pr h)

  bx : Module.Basis Bx ℂ_[l] LA
  bx_eig : ∀ a x, oL a (bx x) = slx x a • bx x

  sle : Ex → (𝓞 E →+* ℂ_[l])
  be : Module.Basis Ex ℂ_[l] (ℂ_[l] ⊗[ℤ] Λ)
  be_eig : ∀ a e, oW l E Λ a (be e) = sle e a • be e

  th : 𝓞 E →+* 𝓞 E
  mu : HA →ₗ[ℂ_[l]] (ℂ_[l] ⊗[ℤ] Λ) →ₗ[ℂ_[l]] Y.H
  mu_bal : ∀ a h w, mu (oH a h) w = mu h (oW l E Λ (th a) w)

  fil : Y.Fil = Submodule.span ℂ_[l] {v | ∃ h w, pr h = 0 ∧ v = mu h w}

  letters : ∀ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id → ∃ b : Module.Basis σ ℂ_[l] (Y.H ⧸ Y.Fil),
    ∀ u, b u = Y.Fil.mkQ (mu (sA (bx (lx u))) (be (le u)))

  all_pairs : ∀ x e, slx x = (sle e).comp th → ∃ u, lx u = x ∧ le u = e

  EL_eq : Y.EL = {L | ∃ sA : LA →ₗ[ℂ_[l]] HA, pr ∘ₗ sA = LinearMap.id ∧ (∀ a, sA ∘ₗ oL a = oH a ∘ₗ sA) ∧
    ∀ u, L u = mu (sA (bx (lx u))) (be (le u))}

attribute [instance] PtTie.acgHA PtTie.modHA PtTie.acgLA PtTie.modLA

def wJ (j : ℕ) : ℝ := ∑ ρ : D.what₂.Tau, DV.wSz D j ρ

def wMax : ℝ := (SizeData₂.lifts D).fold max 0 (wJ D)

structure ThetaDenominatorData where

  dat : ∀ i j b, Set (D.nexp.Dat i j b)

section Run

variable {D} {CH : NChoice D} (X : LiftErrorLocal.Loc D CH)

def UAt (w : D.what₂.places.Pl) : Prop := ∀ j ∈ LiftErrorLocal.lifts D, ∀ b : Bool,
  IntegralHeckeForms.eThPMt D.nexp (CH.twI w) j b (CH.k' w) (CH.Q w) (X.psiW w b) ≤ LiftErrorLocal.twistV0Submodule D CH w j b ∧
    (D.what₂.Ij (D.what₂.muTw w) j (LiftErrorLocal.plS CH w b) : ℝ) ≤
      (D.what₂.places.ramIdx (LiftErrorLocal.plS CH w b) : ℝ) * X.IsgTw w j b

end Run

structure ONObj (CH : NChoice D) (Xd : DivX D) where
  X : LiftErrorLocal.Loc D CH
  X' : LiftErrorLocal.Loc D CH

  I_eq : X'.I = X.I
  c6 : CartierLocalBounds.Loc D Xd X.P6
  c6' : CartierLocalBounds.Loc D Xd X'.P6
  T : ThetaDenominatorData D

end Formalism.MainNotions.PDVN

end
