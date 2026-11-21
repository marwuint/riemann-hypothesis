import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsAdditiveLiftIff

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.Cris GlobalTheory.DeRham GlobalTheory.RealMult GlobalTheory.LatVal GlobalTheory.LatJet
attribute [local instance] Over.cartesianMonoidalCategory

set_option autoImplicit false
noncomputable section
open TensorProduct

namespace GlobalTheory.LatJet.JetFil

variable {F : Type} [Field F] [NumberField F] {𝔠 : FracId F} {R : Type} [CommRing R] {I : Type} [Fintype I] {n : ℕ}
  {J : JetRing R I n} {X : Obj F 𝔠 (Sp R)}
  {m : GrpMor (dp0 R) (𝟙 _) X.A J.κ (spMap J.π) X.A (algebraMap R J.B) (𝟙 _) (Over.Hom.left (𝟙 X.A))}

theorem finite_idx : Finite (Idx I n) :=
  Finite.of_injective (fun ν : Idx I n ↦ fun i ↦ (⟨ν.1 i, Nat.lt_succ_of_le
      ((Finset.single_le_sum (fun j _ ↦ Nat.zero_le (ν.1 j)) (Finset.mem_univ i)).trans ν.2)⟩ : Fin (n + 2)))
    fun a b h ↦ Subtype.ext (funext fun i ↦ by simpa using congrFun h i)

noncomputable def fintypeIdx : Fintype (Idx I n) := @Fintype.ofFinite _ finite_idx

attribute [local instance] fintypeIdx

def co (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) : HdR X.A where
  toFun c := J.b.repr (d (m.pull c)) ν
  map_add' a b := by simp only [map_add, Finsupp.add_apply]
  map_smul' r c := by
    rw [LinearMap.map_smulₛₗ, map_smul, smul_eq_mul, ← Algebra.smul_def, map_smul, Finsupp.smul_apply,
      RingHom.id_apply]

theorem co_apply (hm : m.IsBC) (ν : Idx I n) (d : Crys J.κ (spMap J.π) X.A) (c : primDR X.A) :
    co hm ν d c = J.b.repr (d (m.pull c)) ν := rfl

variable {N : I → Module.End R (HdR X.A)}

end GlobalTheory.LatJet.JetFil

namespace GlobalTheory.LatJet

end GlobalTheory.LatJet
