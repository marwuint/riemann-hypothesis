import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.MapCSmulMulVec

noncomputable section

open PowerSeries

namespace GlobalTheory.NB

namespace Fr

variable {l : ℕ} {O : Type} [CommRing O] (R : Fr l O)

def pt (k : ℕ) (τ : Fin R.e) : O⟦X⟧ := (R.φ ^ k) (X - C (R.ϖ τ))

def OrdGe (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (f g : O⟦X⟧) (a y : ℕ), (l : O⟦X⟧) ^ y ∈ Ideal.span {f, π} ∧ 0 ≤ (a : ℤ) + i ∧
    R.ι (f * π ^ a) * x = R.ι (π ^ ((a : ℤ) + i).toNat * g)

def ConstMod (π : O⟦X⟧) (i : ℤ) (x : R.EE) : Prop :=
  ∃ (y : ℕ) (c : O), R.OrdGe π i ((l : R.EE) ^ y * x - algebraMap O R.EE c)

def cst {r : ℕ} (a : Fin r → O) : Fin r → R.EE := fun k => algebraMap O R.EE (a k)

variable [IsDomain O]

end Fr

def winU (b S η : ℕ) : Set ℤ := Set.Icc (b : ℤ) (b + S) ∪ Set.Icc (-(η : ℤ)) η

def winD (b S η : ℕ) : Set ℤ := Set.Icc (-((b : ℤ) + S)) (-(b : ℤ)) ∪ Set.Icc (-(η : ℤ)) η

def win (up : Bool) (b S η : ℕ) : Set ℤ := if up then winU b S η else winD b S η

namespace Fr

end Fr

namespace Sys

end Sys

namespace Hom

variable {l : ℕ} {O : Type} [CommRing O] {R : Fr l O} {n r r' : ℕ} {S : Sys R n r} {S' : Sys R n r'}
  (F : Hom S S')

def Good : Prop := F.Onto ∧ ∀ i, ∃ a : ℕ, F.Kills i ((l : O⟦X⟧) ^ a)

end Hom

end GlobalTheory.NB
