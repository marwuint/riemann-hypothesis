import Formalism.WachLatticeTwists.SandwichH1Classes.Statement

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology

open Matrix Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic Polynomial

structure TateTr (ℓ : ℕ) [Fact ℓ.Prime] where
  Om : Type
  Oi : Type
  [cOm : CommRing Om]
  [cOi : CommRing Oi]
  [a1 : Algebra ℤ_[ℓ] Om]
  [a2 : Algebra ℤ_[ℓ] Oi]
  [a3 : Algebra Om Oi]
  [tw : IsScalarTower ℤ_[ℓ] Om Oi]
  pr : Oi →ₗ[Om] Om
  pr_alg : ∀ a, pr (algebraMap Om Oi a) = a
  g0 : Oi →ₐ[Om] Oi
  pr_comp_g_zero : ∀ y, pr (g0 y) = pr y

attribute [instance] TateTr.cOm TateTr.cOi TateTr.a1 TateTr.a2 TateTr.a3 TateTr.tw

namespace TateTr

variable {ℓ : ℕ} [Fact ℓ.Prime] (Tt : TateTr ℓ)

def Vi {r : ℕ} (Vm : Matrix (Fin r) (Fin r) Tt.Om) (w : ℤ_[ℓ]ˣ) (i : ℤ) :
    Matrix (Fin r) (Fin r) Tt.Om :=
  algebraMap ℤ_[ℓ] Tt.Om ((w ^ i : ℤ_[ℓ]ˣ) : ℤ_[ℓ]) • Vmᵀ

end TateTr

end Formalism.RepresentationBoundsCohomology.CyclotomicTwistCohomology
