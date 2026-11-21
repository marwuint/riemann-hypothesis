import Mathlib

noncomputable section

namespace MassDataIdxSpl

variable {K T : Type} [Field K] [CommRing T] [Algebra K T] (θ : T ≃ₐ[K] K × K) {n : Type}

def pr1 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).1
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

def pr2 : (n → T) →ₗ[K] (n → K) where
  toFun v i := (θ (v i)).2
  map_add' v w := by funext i; simp
  map_smul' c v := by funext i; simp

theorem fst_apply_alt (v : n → T) (i : n) : pr1 θ v i = (θ (v i)).1 := rfl
theorem snd_apply_alt (v : n → T) (i : n) : pr2 θ v i = (θ (v i)).2 := rfl

variable {ι : Type} (Y : ι → n → T) (s : Set ι)

end MassDataIdxSpl
