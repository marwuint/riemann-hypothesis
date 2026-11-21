import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CommuteIsNilpotentOfUnipotent

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial GlobalTheory.Pst
  GlobalTheory.WeilDeligne TensorProduct Module GlobalTheory.Pst.DpstMap

namespace GlobalTheory.Pst.DmapNonzero

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l} {LL : Type} [Field LL] [Algebra ℚ_[l] LL]
  {V : Type} [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

def subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V) (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) :
    Representation LL ↥(GK K) ↥S where
  toFun g := (ρ g).restrict (hS g)
  map_one' := LinearMap.ext fun v => Subtype.ext (by simp)
  map_mul' g h := LinearMap.ext fun v => Subtype.ext (by simp)

@[simp] theorem coe_subRep (ρ : Representation LL ↥(GK K) V) (S : Submodule LL V)
    (hS : ∀ g, ∀ v ∈ S, ρ g v ∈ S) (g : ↥(GK K)) (v : ↥S) : ((subRep ρ S hS g v : ↥S) : V) = ρ g v := rfl

theorem tensV_eq_rTensor {V' : Type} [AddCommGroup V'] [Module LL V'] [Module ℚ_[l] V']
    [IsScalarTower ℚ_[l] LL V'] (f : V →ₗ[LL] V') (x : V ⊗[ℚ_[l]] Bst P) :
    tensV P f x = (f.restrictScalars ℚ_[l]).rTensor (Bst P) x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.Pst.DmapNonzero

