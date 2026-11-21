import Mathlib

noncomputable section

namespace PI.UnimodularOrthogonalQ2

open NumberField

def OKpair (K : Type) [Field K] [NumberField K] (c : K →+* K) (p : ℕ) [Fact p.Prime] (τ : K →+* ℂ_[p]) :
    Set (ℂ_[p] × ℂ_[p]) :=
  closure (Set.range fun a : 𝓞 K => (τ (a : K), τ (c (a : K))))

def hP {p : ℕ} [Fact p.Prime] {κ : Type} [Fintype κ] (x y : κ → ℂ_[p] × ℂ_[p]) : ℂ_[p] × ℂ_[p] :=
  ∑ k, x k * (y k).swap

def IsBasisOver {p : ℕ} [Fact p.Prime] (O : Set (ℂ_[p] × ℂ_[p])) {κ ι : Type} [Fintype ι]
    (Y : Set (κ → ℂ_[p] × ℂ_[p])) (b : ι → κ → ℂ_[p] × ℂ_[p]) : Prop :=
  (∀ e, b e ∈ Y) ∧ ∀ y ∈ Y, ∃! a : ι → ℂ_[p] × ℂ_[p], (∀ e, a e ∈ O) ∧ y = fun k => ∑ e, a e * b e k

end PI.UnimodularOrthogonalQ2
