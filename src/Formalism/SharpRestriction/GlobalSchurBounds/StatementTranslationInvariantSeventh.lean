import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.ParConsts
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.IsDiscriminantTwelfthRootOfIdealLattice
import Formalism.SharpRestriction.GlobalSchurBounds.TaylorLogMetric
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLatticesGL3

noncomputable section

namespace Formalism.MainNotions.GL3r7

section A

open NumberField Formalism.BasicNotions Classical Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

def PhV {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι σ : Type*} [Fintype κ] [Fintype ι]
    (b : ι → κ → ℂ_[p] × ℂ_[p]) (w : ι → MvPowerSeries σ ℂ_[p]) : MvPowerSeries σ ℂ_[p] :=
  ∑ k, g.phAt (g.lin (fun e => (b e k).1) w)

def sdL {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  g.PhOn (Sum.elim a a') - PhV g a (fun e => Xv (Sum.inl e)) - PhV g a' (fun e => Xv (Sum.inr e))

def sdR {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (g.mulBy (hP (a f) (a' f')).1 (Xv (Sum.inl f))) (Xv (Sum.inr f'))

def sdR' {p : ℕ} [Fact p.Prime] (g : G1 p) {κ ι ι' : Type*} [Fintype κ] [Fintype ι] [Fintype ι']
    (a : ι → κ → ℂ_[p] × ℂ_[p]) (a' : ι' → κ → ℂ_[p] × ℂ_[p]) : MvPowerSeries (ι ⊕ ι') ℂ_[p] :=
  ∑ f, ∑ f', g.be (Xv (Sum.inl f)) (g.mulBy (hP (a f) (a' f')).2 (Xv (Sum.inr f')))

end A

section Z

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric

theorem IntAt.mono {D : D7} {T : Tor D} {p : ℕ} [Fact p.Prime] {lam : Qbar →+* ℂ_[p]} {N N' : ℕ}
    {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)} {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)}
    {Cmb Cmb' : MvPowerSeries (D.what₂.Tau × Fin N' × Fin N) ℂ_[p] → Prop} (h : ∀ F, Cmb' F → Cmb F)
    (H : StandardLatticesGL3.IntAt D T lam L L' Cmb) : StandardLatticesGL3.IntAt D T lam L L' Cmb' := by
  refine ⟨fun hp F hF => H.1 hp F (h F hF), fun hp => ?_⟩
  obtain ⟨S, hS, u, hu, hu', H2⟩ := H.2 hp
  exact ⟨S, hS, u, hu, hu', fun P P' a b c d F hF => H2 P P' a b c d F (h F hF)⟩

end Z

end Formalism.MainNotions.GL3r7
