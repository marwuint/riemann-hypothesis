import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.FramePositiveSum

open MeasureTheory ValuativeRel Matrix

noncomputable section
namespace GlobalTheory.SymChain
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.IndefiniteRowSideFullHecke.FramePositiveSum

structure SymData (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (s κ : ℕ) where

  ψ : AddChar k Circle

  ϖ : kˣ

  ρ : ℕ

  P : TypeDatum k (Fin κ ⊕ Fin (s + 1))

  μ : ℕ → kˣ →* ℂˣ
  tame : ∀ j, IsTame (μ j)
  cond : HasConductor ψ 1
  unif : IsUnif ϖ
  odd : s + 1 = 2 * ρ + 1
  sym : IsSymLevel ψ ϖ ρ P

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
variable {s κ : ℕ} (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t]

def FreeTop (ρ : ℕ) {κ l : ℕ} : Fin κ ⊕ Fin l → Fin κ ⊕ Fin l → Prop
  | .inl i, .inl j => i < j
  | .inr i, .inl _ => i.val < ρ
  | .inl _, .inr j => ρ < j.val
  | .inr i, .inr j => i < j

def FreeIx (ρ : ℕ) {κ l j : ℕ} {t : Type} : Ix (Fin κ ⊕ Fin l) t j → Ix (Fin κ ⊕ Fin l) t j → Prop
  | .inl a, .inl b => FreeTop ρ a b
  | .inl _, .inr _ => True
  | .inr _, .inl _ => False
  | .inr p, .inr p' => p.1 ≤ p'.1

namespace SymData

def Pattern : Prop :=
  ∀ j (g : GL (Ix (Fin κ ⊕ Fin (s + 1)) t j) k), g ∈ (S.P.iter t S.μ S.tame j).J ↔
    g ∈ KO k _ ∧ ∀ a b, ¬ FreeIx S.ρ a b → valuation k (g.val a b - (1 : Matrix _ _ k) a b) < 1

abbrev T : Chain k s (XIx (Fin κ) t) (Ix (Fin κ ⊕ Fin (s + 1)) t (s + 2)) := typeChain t S.ϖ S.P S.μ S.tame

def y0 : XIx (Fin κ) t (s + 1) → k := Pi.single (Sum.inl (Sum.inr 0)) ((S.ϖ⁻¹ : kˣ) : k)

def PrLevel : Prop :=
  ∀ j c (h : j + c = s + 1), prX (Cgrp ((S.T t).lev j c h).J 1) = ((S.T t).lev j c h).J.comap (embX c)

def OneCoupling : Prop :=
  (∀ x₀ y, (S.T t).Psi 1 x₀ y ≠ 0 → y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)) ∧
  (∀ x₀ y, y - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ) → (S.T t).Psi 1 x₀ y = (S.T t).Psi 1 x₀ (S.y0 t)) ∧
  ∀ γ : GL (XIx (Fin κ) t (s + 1)) k, embX 0 γ ∈ ((S.T t).lev (s + 1) 0 rfl).J →
    γ.val *ᵥ S.y0 t - S.y0 t ∈ box (XIx (Fin κ) t (s + 1)) (1 : kˣ)

def SupportOne : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    h ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)) → ∀ x₀ e,
      (S.T t).Phi j (c + 1) (by omega) ((h⁻¹).val * affPt 1 x₀ e) ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ ((S.T t).lev (j + 1) (c + 1) (by omega)).J, h = r * u

variable [MeasurableSpace k] [BorelSpace k] (ν : Measure k)

def OneClass : Prop :=
  ∀ j c (H : j + 1 + c = s) (h : GL (XIx (Fin κ) t (j + 1) ⊕ Fin (c + 1)) k),
    flat S.ψ ν (S.μ (j + 1)) ((S.T t).Phi j (c + 1) (by omega)) 1 h ≠ 0 →
      ∃ r ∈ R k (XIx (Fin κ) t (j + 1)) (c + 1) 1, ∃ u ∈ stabLat ((S.T t).bas (j + 1) (c + 1) (by omega)), h = r * u

def OneIndex : Prop :=
  ∀ j c (h : j + 1 + c = s), ∀ β ∈ (S.T t).idx S.ψ ν j c h 1,
    β = DoubleCoset.mk (R k (XIx (Fin κ) t (j + 1)) (c + 1) 1) ((S.T t).lev (j + 1) (c + 1) (by omega)).J 1

end SymData

def AtMostOne : Prop :=
  ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    [MeasurableSpace k] [BorelSpace k] (ν : Measure k), IsUnitVol ν →
    ∀ (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
      S.OneIndex t ν ∧ S.PrLevel t ∧ S.OneCoupling t

end GlobalTheory.SymChain
