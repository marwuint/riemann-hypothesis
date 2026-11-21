import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.SemidirectVolume.HermitianIsotropicProjComplement

noncomputable section

namespace PI.VolSemiDirect.W.PG

open Formalism.UG

variable {A : Type} [CommRing A] {n : Type} [Fintype n] [DecidableEq n] {r : ℕ}

namespace Dat

variable (D : Dat A n r)

def L (w : Fin r → n → A) (s : Fin r → Fin r → A) : (n → A) →ₗ[A] (n → A) :=
  LinearMap.id + ∑ b, (D.hL (D.e b)).smulRight (w b + ∑ a, s a b • D.e a) -
    ∑ a, ((D.hL (w a)).comp D.pW).smulRight (D.e a)

theorem L_apply (w : Fin r → n → A) (s : Fin r → Fin r → A) (v : n → A) :
    D.L w s v = v + ∑ b, D.h (D.e b) v • (w b + ∑ a, s a b • D.e a) -
      ∑ a, D.h (w a) (D.pW v) • D.e a := by
  simp only [L, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, LinearMap.sum_apply,
    LinearMap.smulRight_apply, LinearMap.comp_apply]
  rfl

variable {D}

theorem pX_of_span (H : D.Hyp) {x : n → A} (hx : x ∈ Submodule.span A (Set.range D.e)) :
    D.pX x = x := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨b, rfl⟩ := hx
    rw [pX_apply]
    simp [fe H]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, hx]

end Dat

end PI.VolSemiDirect.W.PG
