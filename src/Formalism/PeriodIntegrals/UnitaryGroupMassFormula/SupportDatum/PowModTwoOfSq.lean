import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.LocalGroupInFamilyNontrivial

noncomputable section

namespace PI.SupportDatumW

open NumberField IsDedekindDomain Formalism.MainNotions.S Formalism.MainNotions.S.LocalSplitGroups ValuativeRel
open scoped BigOperators ComplexOrder
open Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem twist_mul {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) (x : (D.s.atP p).Ep) :
    twist p s x = x * twist p s 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp [mul_comm]

theorem twist_one_pow {D : Formalism.BasicNotions.D7} (p : PlF D) (s : ℕ) :
    twist p s (1 : (D.s.atP p).Ep) = twist p 1 (1 : (D.s.atP p).Ep) ^ s := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

theorem twist_sq {D : Formalism.BasicNotions.D7} (p : PlF D) :
    twist p 1 (1 : (D.s.atP p).Ep) ^ 2 = 1 := by
  unfold twist
  rcases (D.s.atP p).split with _ | sg
  · simp
  · apply sg.e.injective
    ext <;> simp

def hF (D : Formalism.BasicNotions.D7) (δ : ∀ p : PlF D, (D.s.atP p).Fp) (p : PlF D) (a s : ℕ) : (D.s.atP p).Ep :=
  Ring.inverse ((algebraMap (D.s.atP p).Fp (D.s.atP p).Ep (δ p) * (D.s.atP p).ιE (uP p : D.host.E)) ^
    (nu D.R.rS a (a + s - 1))) * twist p s 1 * Ring.inverse (qE p)

end PI.SupportDatumW
