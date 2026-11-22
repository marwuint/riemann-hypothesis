import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.FiniteDimensionalMram

noncomputable section

namespace GlobalTheory.Core.Rk

open Formalism.BasicNotions

def SameTops (D D' : D7) : Prop :=
  ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau) (t : D.host.TT) (t' : D'.host.TT) (h : 0 < D.R.k) (h' : 0 < D'.R.k),
    (D.eTau τ : D.R.GG) = D.R.tau1 t → (D'.eTau τ' : D'.R.GG) = D'.R.tau1 t' →
    (t : D.R.A).val = (t' : D'.R.A).val →
      (D.hc τ).u ⟨0, h⟩ = (D'.hc τ').u ⟨0, h'⟩ ∧
        (D.hc τ).u ⟨D.R.k - 1, by omega⟩ = (D'.hc τ').u ⟨D'.R.k - 1, by omega⟩

structure SameHost (D D' : D7) : Prop where

  R_eq : D.R = D'.R

  TT_eq : D.host.TT.image Formalism.HC.Frame.A.val = D'.host.TT.image Formalism.HC.Frame.A.val
  realisedChain_torus_eq : D.host.T2 = D'.host.T2
  q_eq : D.host.q = D'.host.q
  d_eq : D.host.d = D'.host.d
  g_eq : D.host.g = D'.host.g
  pde_eq : D.host.pde = D'.host.pde
  pde'_eq : D.host.pde' = D'.host.pde'

  QS_eq : D.host.QS = D'.host.QS

  art_eq : ∀ (p : ℕ) (h : Nat.Coprime p D.host.condN) (h' : Nat.Coprime p D'.host.condN),
    (D.host.art (ZMod.unitOfCoprime p h)).1 = (D'.host.art (ZMod.unitOfCoprime p h')).1 ∧
      (D.R.iotaInv (D.host.art (ZMod.unitOfCoprime p h)).2).val = (D'.R.iotaInv (D'.host.art (ZMod.unitOfCoprime p h')).2).val

theorem SameHost.refl (D : D7) : SameHost D D := ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, fun _ _ _ => ⟨rfl, rfl⟩⟩

structure SameWord (D : D7) (u : D.what₂.Word) (D' : D7) (u' : D'.what₂.Word) : Prop where
  host : SameHost D D'
  unitVector_val_eq : D.host.u0.val = D'.host.u0.val
  hc_eq : ∀ (τ : D.what₂.Tau) (τ' : D'.what₂.Tau), HEq (D.eTau τ) (D'.eTau τ') → HEq (D.hcW u τ) (D'.hcW u' τ')

structure Pts where

  Ix : ℝ → Type

  D : ∀ x, Ix x → D7

  Ix_ne : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x)

  same : ∀ x (i i' : Ix x), SameHost (D x i) (D x i')

namespace Pts

theorem ne_of_forall {Ix : ℝ → Type} (h : ∀ x, Nonempty (Ix x)) : ∀ y, ∃ x, y ≤ x ∧ Nonempty (Ix x) :=
  fun y => ⟨y, le_rfl, h y⟩

def single (D : ℝ → D7) : Pts :=
  ⟨fun _ => Unit, fun x _ => D x, ne_of_forall fun _ => ⟨()⟩, fun _ _ _ => SameHost.refl _⟩

variable (F : Pts)

def SomeAt (Q : ℝ → ∀ D : D7, D.what₂.Word → Prop) : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀) ∧ ∃ u, Q x (F.D x i) u

def Covered : Prop :=
  ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → ∀ (i₀ : F.Ix x) (u₀ : ℕ), u₀ < (F.D x i₀).R.n →
    ∃ i : F.Ix x, (F.D x i).host.u0.val = u₀ ∧ SameTops (F.D x i) (F.D x i₀)

variable {F}

theorem SomeAt.exists {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) :
    ∃ x₀ : ℝ, ∀ x, x₀ ≤ x → Nonempty (F.Ix x) → ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h
  refine ⟨x₀, fun x hx ⟨i₀⟩ => ?_⟩
  obtain ⟨i, -, -, u, hu⟩ := h x hx i₀ 0 (F.D x i₀).R.ord_pos
  exact ⟨i, u, hu⟩

theorem SomeAt.exists_ge {Q : ℝ → ∀ D : D7, D.what₂.Word → Prop} (h : F.SomeAt Q) (y : ℝ) :
    ∃ x, y ≤ x ∧ ∃ (i : F.Ix x) (u : (F.D x i).what₂.Word), Q x (F.D x i) u := by
  obtain ⟨x₀, h⟩ := h.exists
  obtain ⟨x, hx, hne⟩ := F.Ix_ne (max x₀ y)
  exact ⟨x, le_of_max_le_right hx, h x (le_of_max_le_left hx) hne⟩

end Pts

namespace Pts

end Pts

end GlobalTheory.Core.Rk

end
