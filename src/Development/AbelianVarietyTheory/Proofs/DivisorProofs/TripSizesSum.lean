import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

noncomputable section

open GlobalTheory.SmGL

namespace GlobalTheory.CuspBlock

variable (k : Type) [CommRing k]

variable {k} in

def glCast {a b : ℕ} (h : a = b) : GL (Fin a) k →* GL (Fin b) k := h ▸ MonoidHom.id _

@[simp] theorem glCast_rfl {a : ℕ} : glCast (k := k) (rfl : a = a) = MonoidHom.id _ := rfl

end GlobalTheory.CuspBlock
