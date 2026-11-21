import Mathlib
import GroundTheory.AutomorphicForms.GKModules.SmoothVectors
import GroundTheory.AutomorphicForms.GKModules.RightRegular
import GroundTheory.AutomorphicForms.DiscreteSpectrumAbstract
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.BasicForm

noncomputable section

open GlobalTheory.BorelCoh GroundTheory.Automorphic

namespace GlobalTheory.Mt

variable {𝔸 : Type} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸] [FiniteDimensional ℝ 𝔸]

structure CartanData (G : Subgroup 𝔸ˣ) (𝔤 : Submodule ℝ 𝔸) where

  lie : IsExpLieAlgebra G 𝔤

  closed : IsClosed (G : Set 𝔸ˣ)

  K : Subgroup G
  compact : IsCompact (K : Set G)

  k : Submodule ℝ 𝔤

  p : Submodule ℝ 𝔤
  isCompl : IsCompl k p
  bracket_kk : ∀ X ∈ k, ∀ Y ∈ k, lie.bracket X Y ∈ k
  bracket_kp : ∀ X ∈ k, ∀ Y ∈ p, lie.bracket X Y ∈ p
  bracket_pp : ∀ X ∈ p, ∀ Y ∈ p, lie.bracket X Y ∈ k
  Ad_p : ∀ κ ∈ K, ∀ Y ∈ p, lie.Ad κ Y ∈ p
  expG_k : ∀ X ∈ k, lie.expG X ∈ K

  cartan : ∀ g : G, ∃! x : p × K, g = lie.expG (x.1 : 𝔤) * (x.2 : G)

  smooth_cartan : ∀ ℓ : 𝔤 →L[ℝ] ℂ, lie.IsSmoothFun (F := ℂ) fun g => ℓ ((cartan g).exists.choose.1 : 𝔤)

  B : LinearMap.BilinForm ℝ 𝔤
  B_symm : ∀ X Y, B X Y = B Y X
  B_Ad : ∀ g X Y, B (lie.Ad g X) (lie.Ad g Y) = B X Y
  B_p : ∀ X ∈ p, X ≠ 0 → 0 < B X X
  B_k : ∀ X ∈ k, X ≠ 0 → B X X < 0
  B_kp : ∀ X ∈ k, ∀ Y ∈ p, B X Y = 0

namespace CartanData

variable {G : Subgroup 𝔸ˣ} {𝔤 : Submodule ℝ 𝔸} (D : CartanData G 𝔤)

section Unitary

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

def toBanach (π : UnitaryRep G H) : BanachRep G H :=
  ⟨(unitary (H →L[ℂ] H)).subtype.comp π.toHom, fun v => π.continuous_orbit' v⟩

abbrev SmV (π : UnitaryRep G H) : Submodule ℂ H := D.lie.smoothVectors (toBanach π)

variable {d : ℕ}

end Unitary

end CartanData

end GlobalTheory.Mt
