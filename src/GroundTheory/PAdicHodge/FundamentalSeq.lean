import Mathlib
import GroundTheory.PAdicHodge.FundamentalSeqBCris
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.PAdicHodge

namespace ACris

section Packaging

variable (k : Type*) {B : Type*} (D E : Type*) [Field k] [CommRing B] [Algebra k B] [CommRing D]
  [CommRing E] [Algebra k D] [Algebra D E] [Algebra k E] [IsScalarTower k D E]

variable {k} in

def fixedSubspace (φ : B →+* B) (hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q) :
    Submodule k B where
  carrier := {x | φ x = x}
  add_mem' {x y} hx hy := by
    simp only [Set.mem_ofPred_eq] at hx hy ⊢
    rw [map_add, hx, hy]
  zero_mem' := map_zero φ
  smul_mem' q x hx := by
    simp only [Set.mem_ofPred_eq] at hx ⊢
    rw [Algebra.smul_def, map_mul, hφ, hx]

theorem mem_fixedSubspace {φ : B →+* B} {hφ : ∀ q : k, φ (algebraMap k B q) = algebraMap k B q}
    {x : B} : x ∈ fixedSubspace φ hφ ↔ φ x = x :=
  Iff.rfl

variable {k D E}

end Packaging

variable {p : ℕ} [hp : Fact p.Prime]

local notation "𝔹" => BDeRhamPlus (normInteger ℂ_[p]) p
local notation "𝔹dR" => BDeRham (normInteger ℂ_[p]) p

variable {ε : PreTilt (normInteger ℂ_[p]) p} (hε : PreTilt.untilt ε = 1)
  (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[p]) p) p).symm ε) ≠ 1)

end ACris

end GroundTheory.PAdicHodge
